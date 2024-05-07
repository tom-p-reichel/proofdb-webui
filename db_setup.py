from prism.language.heuristic.parser import HeuristicParser
import asyncio as aio
from coqtop import CoqProcess
from collections import defaultdict
import traceback
import sqlite3 as sql
import os
from pathlib import Path
import re
import random
import tqdm
import os
import glob
import itertools

async def map_n(f,objs,n=10,timeout=None):
    procs = set()
    finished = []
    for o in tqdm.tqdm(objs):
        procs.add(aio.create_task(f(o)))
        while len(procs)>=n:
            done,procs = await aio.wait(procs,return_when=aio.FIRST_COMPLETED)
            for x in done:
                finished.append(await x)
    done,pending = await aio.wait(procs,timeout=timeout)
    for x in done:
        finished.append(await x)
    for x in pending:
        x.cancel()
    return finished

async def runcmd(cmd):
    proc = await aio.create_subprocess_shell(
        cmd,
        stdout=aio.subprocess.PIPE,
        stderr=aio.subprocess.PIPE)
    stdout, stderr = await proc.communicate()
    return proc.returncode,stdout



# INIT SQLITE DB ****************************************************
con = sql.connect("log.db")

cur = con.cursor()

# i want to know EXACTLY what commits of things
# bad things happened on
cur.execute("""
CREATE TABLE IF NOT EXISTS logs (
    time INTEGER,
    commithash TEXT,
    modelrevision TEXT,
    uuid TEXT,
    cohort TEXT,
    type TEXT,
    value TEXT
);""")

cur.close()

con.close()


# DETERMINE FILE OWNERSHIP ***********************************************


sw = os.environ.get("OPAM_SWITCH_PREFIX")

files = glob.glob(sw+"/lib/coq/**/*.v",recursive=True)

files = sorted(files)

async def determine_owners(files):
    packages = (await runcmd("opam list --column=\"package\" -s"))[1].split()

    async def get_package_files(f):
        return (f,(await runcmd(f"opam show --list-files {f}"))[1].split())

    package_files = (await map_n(get_package_files,(y.decode().split(".")[0] for y in packages)))
    
    file_to_package = {}

    for package,file in itertools.chain.from_iterable(itertools.product([x[0]],*x[1:]) for x in package_files):
        file_to_package[file.decode()] = package

    return file_to_package


def field_getter(field):
    async def g(package):
        ret, stdout = await runcmd(f"opam show -f {field} {package}")
        if ret != 0 or len(stdout) == 0:
            return None
        stdout = stdout.decode().strip()
        if stdout.startswith("\"") and stdout.endswith("\""):
            return package,stdout[1:-1]
        return package,stdout
    return g

file_owners = aio.run(determine_owners(files))

packages = list(set(file_owners.values()))

print("got file owners")

package_licenses = dict(aio.run(map_n(field_getter("license"),packages)))

package_homepages = dict(aio.run(map_n(field_getter("homepage"),packages)))

# RIP THEOREM INFO **************************************


parser = HeuristicParser()

cmds = ["Lemma","Theorem","Corollary","Fact","Remark","Proposition","Property"]#,"Instance"]

name_pattern_gen = lambda x: re.compile(fr"(?:^|\s)*(?:{'|'.join(x)})\s+([^\s:]+)")

thm_name_pattern = name_pattern_gen(cmds)

# TODO: check to see if this causes bad things
# e.g. modules named Type??

possible_module_names = re.compile(r"End ([^\s.=]+)\s*.")

def get_module_pattern(names):
    name_pattern = "(" + "|".join(re.escape(x) for x in names) + ")"
    module_pattern = re.compile(fr"[^.]*Module[^.=]*\s{name_pattern}(?:\s+[^.]*)?\.(\s+|.+?\.\s+)End\s+\1\s*\.",flags=re.DOTALL)
    return module_pattern

theorems = defaultdict(list)

db = []

def moduleize(source):
    modules = []
    possible_names = possible_module_names.findall(source)
    modules.extend(get_module_pattern(possible_names).finditer(source))
    children = []
    for module in modules:
        children.extend(moduleize(module.group(2)))
    return modules+children

def fs2coq(path):

    path = ".".join(x for x in path[:-2].split("/"))

    if ".lib.coq" in path:
        # sometimes the paths are absolute starting from root for some reason???
        # not forcing the llm to know the absolute directory on the system it's running on...
        if "user-contrib" in path:
            cut_at = ".lib.coq.user-contrib."
            prefix = ""
        elif "theories" in path:
            cut_at = ".lib.coq.theories."
            prefix = "Coq."

        path = prefix+path[path.index(cut_at)+len(cut_at):]

    return path


#introduce_all_ltac = """repeat (try intros; try match goal with | |- exists unnamed : ?H, _ => let ident := fresh unnamed in evar (ident:H); exists ident end)."""
print_hyps_ltac = """tryif (multimatch goal with H:?T |- _ => idtac H ":@:" T; fail end) then idtac else idtac."""
coq_lines_pattern = re.compile(r"(^[^\s][^\n]*(?:\n^\s[^\n]+)*)",flags=re.M)
coq_init_minimal = 'Require Import Coq.Init.Logic. Require Import Coq.Init.Ltac. Require Import Coq.Init.Tactics. Inductive TruthLike : Prop := TruthLikeConstructor.'

hyps_found = 0

async def process_defs(f):
    global theorems
    code,stdout = await runcmd(f"coqdoc --no-glob --no-externals --raw -s -g --stdout \"{f}\"")
    docs = stdout.decode()
    # QUIRK: prism code can't handle parsing a document with no sentences.
    # and we can't just check if docs is empty because sometimes it's just a comment.
    # so we're going to add a dummy sentence here.
    # TODO: fix the upstream issue with empty sentences instead of doing this.
    docs = "Compute (1+1).\n"+docs
    module_stack = moduleize(docs)
    try:
        for s in HeuristicParser._get_sentences(docs):
            ss = str(s)
            path = []
            if thm_name_pattern.match(ss) is not None:
                for mod in module_stack:
                    span = mod.span()
                    if span[0]<=s.start<s.end<=span[1]:
                        path.append(mod.group(1))
                theorems[f].append((path,ss))
                            
    except Exception:
        print(f"whoops in {f}:")
        print(traceback.format_exc())
        print(docs)

    flags = []
    coq = CoqProcess()
    
    filepath = fs2coq(f)

    _,err = await coq.run(f"Timeout 30 Require Import {filepath}.",return_stderr=True)
    if "Error" in err:
        coq.close()
        coq = CoqProcess("-noinit")
        if "Error" in (await coq.run(f"Timeout 30 Require Import {filepath}.",return_stderr=True))[1]:
            print("import failed",err)
            if f in theorems:
                del theorems[f]
            return
        flags = ["-noinit"]

    env = {}
    for c in cmds:
        env.update(coq.env_regex.findall(await coq.run(f"Search is:{c} inside {filepath}.")))

    global example
    env = {(await coq.locate(k)):v for k,v in env.items()}
    example = env

    env_expected = {filepath+"."+".".join(path+[thm_name_pattern.match(thm).group(1)]):i for i,(path,thm) in enumerate(theorems[f])}
    if (set(env_expected.values())!=set(range(len(env_expected)))):
        # ok, we have a duplicate somehow.
        # TODO: this triggers approximately once during scraping. 
        # fix it!
        print("mysterious duplicate detected in ",f)
    """ 
    try:
        print(f,len(set(env.keys()).intersection(env_expected))/len(env_expected),"keys redetected",len(set(env.keys())-env_expected),"keys newly detected")
    except ZeroDivisionError:
        pass

    """

    weirdos = set()

    for new_thm in env.keys()-env_expected.keys():
        # functor instantiation, instances, other magic plugin bullshit
        assert(new_thm.startswith(filepath))

        theorems[f].append((new_thm[len(filepath)+1:].split(".")[:-1],f"Theorem {new_thm.split('.')[-1]} : {env[new_thm].strip()}."))
        #print("creating new weird theorem",theorems[f][-1])
        weirdos.add(theorems[f][-1][1])

    for dead_thm in sorted(env_expected.keys()-env.keys(),key=lambda x : env_expected[x], reverse=True):
        # functors, local/non-exported things
        #print("nuking unfindable theorem",theorems[f][env_expected[dead_thm]][1],"at index",env_expected[dead_thm])
        assert(thm_name_pattern.match(theorems[f][env_expected[dead_thm]][1]).group(1) == dead_thm.split(".")[-1])
        del theorems[f][env_expected[dead_thm]]

    #await coq.run(coq_init_minimal)
    try:

        for (path,thm) in theorems[f]:
            short_name = thm_name_pattern.match(thm).group(1)
            thm_name = filepath+"."+".".join(path+[short_name])

            if thm_name not in env.keys():
                # TODO: this is a side effect of mysterious duplicates.
                # fix it!
                continue
            _,err = await coq.run(f"""Goal True.
            pose (@{thm_name}) as H.
            let Htype := type of H in cut Htype; clear H.
            1:intros.
            1:apply I.
            repeat (try intros; try match goal with | |- exists unnamed : ?H, _ => let ident := fresh unnamed in evar (ident:H); exists ident end).
            """, return_stderr=True)
            if "Error" in err:
                print(f)
                print(f"setup failed in {filepath} for {thm_name}.")
                print(err)
                coq.close()
                coq = CoqProcess(*flags)
                #await coq.run(coq_init_minimal)
                await coq.run("Require Import {filepath}.")
            else:
                hyps_raw,err = await coq.run(print_hyps_ltac,return_stderr=True)
                assert("Error" not in err)
                #print(hyps_raw)
                global hyps_found
                hyps_found += 1
                if (hyps_found % 1000 == 0):
                    print(hyps_found)
                hyps_parsed = [x.split(" :@: ") for x in coq_lines_pattern.findall(hyps_raw) if x.strip() !=""]
                # QUIRK: if you idtac two things on 'the same line', then idtac occasionally inserts
                # newlines to break the line if it's long enough.
                # most linebreaking logic in coq will INDENT a broken line, allowing us to detect it.
                # but not idtac. for some reason.
                # i don't really care because if the type of an argument is longer than a line then it's not
                # something a user would ever really ask for.
                # TODO: fix this if it matters
                hyps_parsed = [x for x in hyps_parsed if len(x)==2]
                db.append(dict(location=thm_name,
                               filepath=filepath,
                               package=file_owners[f],
                               modpath=".".join(path+[short_name]),
                               name=short_name,
                               text=thm,
                               args=hyps_parsed,
                               weird=(thm in weirdos),
                               license=package_licenses[file_owners[f]],
                               homepage=package_homepages[file_owners[f]]
                          )
                )

                await coq.run("Abort.")
    finally:
        # TODO: this should probably happen throughout the entire time 
        # the coqprocess exists and not just here...
        coq.close(kill=True)

"""
                hyps_parsed = [x.split(" :@: ") for x in coq_lines.findall(hyps) if x.strip() !=""]
                # QUIRK: if you idtac two things on 'the same line', then idtac occasionally inserts
                # newlines to break the line if it's long enough.
                # most linebreaking logic in coq will INDENT a broken line, allowing us to detect it.
                # but not idtac. for some reason.
                hyps_parsed = [x for x in hyps_parsed if len(x)==2]
                thms_hyps[ss] = hyps_parsed

"""

n = 8




aio.run(map_n(process_defs,files,n=n,timeout=60))



from transformers import AutoModelForCausalLM, AutoTokenizer
from transformers.models.llama.modeling_llama import LlamaModel
import torch

model = LlamaModel.from_pretrained("./model/base_model",load_in_4bit=True,bnb_4bit_compute_dtype=torch.float16)
model.load_adapter("./model/adapter/")

tokenizer = AutoTokenizer.from_pretrained("./model/base_model")

#thms_flat = sorted(list(itertools.chain.from_iterable(theorems.values())),key=lambda x: len(x), reverse=True)

db = list(filter(lambda x: len(x["text"]) < 4000, db))

db = sorted(db,key=lambda x : len(x["text"]),reverse=True)

thms_flat = [x["text"] for x in db]

vecs = []
import more_itertools as miter

tokenizer.pad_token = tokenizer.eos_token

import goodinference

vecs = goodinference.embed(model,tokenizer,thms_flat,progress=True)
"""
for x in tqdm.tqdm(list(miter.chunked(thms_flat,10))):
    # batching would be much more efficient!
    with torch.no_grad():
        vecs.append(model(**tokenizer(x,return_tensors="pt",padding=True)).last_hidden_state.cpu())

vecs = torch.vstack([x[:,-1,:] for x in vecs])
"""

vecs = vecs/torch.linalg.norm(vecs,axis=1,keepdims=True)

torch.save(vecs,"./vecs.pt")

import json

json.dump(db,open("./theorems.json","w"))

# generate random projection

import math

bits = int( (( (math.log(len(db)*0.05**(-0.5)) + math.log(2)/2) / 0.05**2 ) // 64 + 1) * 64 )

proj = torch.zeros([bits,vecs.shape[1]])

proj.normal_()

torch.save(proj,"./db/projection.pt")
