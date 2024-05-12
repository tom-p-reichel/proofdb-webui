from fastapi import FastAPI, Cookie, Query, Request, Body, BackgroundTasks
from fastapi.responses import FileResponse, JSONResponse
from fastapi.staticfiles import StaticFiles
from typing import Annotated
import asyncio as aio
import aiosqlite
import ujson
import time
from transformers import AutoModelForCausalLM, AutoTokenizer
from transformers.models.llama.modeling_llama import LlamaModel
import gc
import re
import itertools
import torch
import ujson
import itertools
import subprocess
import base64
import pickle
import random
import goodinference
import struct
from pathlib import Path
import sys
import base64
import config



if config.use_gpuq:
    import gpuq
    SearchBase = gpuq.Service
else:
    class GPUQStub:
        def __init__(self, **kwargs):
            self.has_setup = False
            self.service_lock = True
        async def run(self,*args,**kwargs):
            if not self.has_setup:
                await self.setup()
                self.has_setup = True
            return await self.f(*args,**kwargs)
    SearchBase = GPUQStub

class GPUSearch(SearchBase):
    async def setup(self):
        self.model = LlamaModel.from_pretrained(config.base,load_in_4bit=True,bnb_4bit_compute_dtype=torch.float16)
        self.model.load_adapter(config.adapter)
        self.tokenizer = AutoTokenizer.from_pretrained(config.base)
        self.tokenizer.pad_token = self.tokenizer.eos_token
        self.vecs = torch.load("./db/vecs.pt",map_location="cuda").half()
        self.projection = torch.load("./db/projection.pt",map_location="cuda").half()


    async def f(self,prompts,search=True,return_search_embed=False):
        loop = aio.get_event_loop()
        

        if search:
            def proc():
                with torch.no_grad():
                    embed = self.model(**self.tokenizer(prompts,return_tensors="pt")).last_hidden_state[0,-1].cuda()
                    embed /= torch.linalg.norm(embed)
                    scores = (self.vecs@embed).cpu()
                    if return_search_embed:
                        return embed,scores
                    else:
                        return scores
        else:
            # this mode jumps through weird hoops to support the coq client.
            def proc():
                vecs = goodinference.embed(self.model,self.tokenizer,prompts,max_tokens=4000,progress=True)
                #vecs /= torch.linalg.norm(vecs,axis=1,keepdim=True)
                print("projecting...")
                bits = torch.sign(vecs.cuda()@self.projection.T)>0
                print("converting to base64...")
                chars = [ base64.b64encode(bytes(x)) for x in
                    (bits.reshape((bits.shape[0],bits.shape[1]//8,8)) * (2**torch.arange(8,dtype=torch.uint8)).cuda()).sum(dim=-1).cpu()
                ]
                print("ready to send!")

                return chars


        return await loop.run_in_executor(None, proc)


    async def cleanup(self):
        del self.model
        del self.vecs
        del self.projection
        gc.collect()
        torch.cuda.empty_cache()



app = FastAPI()

if config.use_docs:
    app.mount("/doc",StaticFiles(directory="./doc"),name="doc")


app.mount("/static",StaticFiles(directory="./static"),name="static")

app.model = GPUSearch(gbs=6)

app.query_cache = {}

with open("./db/theorems.json") as f:
    app.db = ujson.load(f) 


if Path("db/custom_theorem_cache.pk").exists():
    with open("db/custom_theorem_cache.pk","rb") as f:
        app.custom_cache = pickle.load(f)
    print(f"loaded {len(app.custom_cache)} custom theorems")
else:
    app.custom_cache = {}

# logging what version we are in the sqlite db
git_repo_dir = Path(__file__).parent.absolute()
app.commithash = subprocess.check_output("git rev-parse HEAD",shell=True,cwd=git_repo_dir).strip().decode()

# logging what version the model seems to be because we don't track those files in the repo (too big)

cookiestr = Annotated[str, Cookie()]

async def log(uuid,cohort,log_type,value):
    t = int(time.time())
    async with aiosqlite.connect("db/log.db") as db:
        await db.execute("INSERT INTO logs (time,commithash,uuid,cohort,type,value) VALUES (?,?,?,?,?,?)",
            (t,app.commithash,uuid,cohort,log_type,value)
        )
        await db.commit()


# TODO: these manual page mappings are gross and repetitive.
# unfortunately the thing i found to address this
# maps all requests to all subdirectories to a folder--
# but this would break /api/ !
# figure out some other way.
@app.get("/")
async def index():
    return FileResponse("./templates/index.html")

@app.get("/bulma.min.css")
async def index():
    return FileResponse("./templates/bulma.min.css")

@app.get("/jquery.min.js")
async def index():
    return FileResponse("./templates/jquery.min.js")

@app.get("/help")
async def help():
    return FileResponse("./templates/help.html")

@app.get("/about")
async def about():
    return FileResponse("./templates/about.html")




@app.post("/api/feedback")
async def feedback(uuid: cookiestr, cohort: cookiestr, feedback: Annotated[str,Body(...)]):
    # truncate ludicrously long feedback
    await aio.sleep(0.75)
    await log(uuid,cohort,"feedback",feedback[:10000])


app.lookup_loc = {x["location"]:i for i,x in enumerate(app.db)}

app.toplevel_libraries = {x["location"].split(".")[0] for x in app.db}




@app.post("/api/coq-client")
async def coq_client(request:Request):
    
    if not config.allow_client:
        return dict(info="This instance doesn't support calls from your client.")
    

    request = await request.json()
   
    #normal_theorems = [x for x in request["theorems"] if x[0] in app.lookup_loc]
    custom_theorems = [x for x in request["theorems"] if len(x[1]) < 2048]
    
    
    request_length = len(custom_theorems)

    strings = []

    for (name,stmt) in custom_theorems:
        name = name.split(".")[-1]
        if stmt.startswith("(") and stmt.endswith(")"):
            stmt = stmt[1:-1]

        strings.append(f"Theorem {name} : {stmt}.")

    # TODO: sqlite cache
    
    theorem_embeds = {}

    fresh_strings = []
    fresh_indices = []

    for i,s in enumerate(strings):
        if s in app.custom_cache:
            theorem_embeds[custom_theorems[i][0]] = app.custom_cache[s]
        else:
            fresh_strings.append(s)
            fresh_indices.append(i)

    
    vecs = await app.model.run([request["query"]] + fresh_strings, search=False)

    for i,v,s in zip(fresh_indices,vecs[1:],fresh_strings):
        theorem_embeds[custom_theorems[i][0]] = v
        app.custom_cache[s] = v

    if len(fresh_strings) > 150:
        with open("db/custom_theorem_cache.pk","wb") as f:
            pickle.dump(app.custom_cache,f)

    return dict(info="",theorems=theorem_embeds, query=vecs[0])


"""
    #app.custom_blocks.append(vecs.cpu())

    #bid = len(app.custom_blocks)

    #for i_real,i in enumerate(idx):
    #    app.custom_index[custom_theorems[i][0],custom_theorems[i][1]] = (bid,i_real)
    
    query,normal_scores = (await app.model.run([request["query"]],return_search_embed=True))

    custom_scores = vecs@query
    
    custom_ranking = torch.argsort(custom_scores,descending=True)

    normal_ranking_with_globals = torch.argsort(normal_scores,descending=True)


    # only show theorems user has installed
    normal_theorem_idx = {app.lookup_loc[x[0]] for x in normal_theorems}

    normal_ranking = [x for x in normal_ranking_with_globals if x.item() in normal_theorem_idx]


    
    combined_ranking = sorted([(True,x)  for x in range(min(30,len(normal_ranking)))] + [(False,x)  for x in range(min(30,len(custom_ranking)))], key=lambda x: normal_scores[normal_ranking[x[1]]] if x[0] else custom_scores[custom_ranking[x[1]]],reverse=True)
    
    results = []


    for (is_normal,i) in combined_ranking:
        if is_normal:
            results.append(app.db[normal_ranking[i]]["location"]+ ":" + app.db[normal_ranking[i]]["text"])
        else:
            custom_ind = idx[custom_ranking[i]]
            results.append(custom_theorems[custom_ind][0] + ":" + custom_theorems[custom_ind][1])


    response = "\n".join(results)
    
    #vec_fmt = "<"+vecs.shape[1]*"f"


    return {"info":response}
"""

filter_pattern = re.compile(r"([^\s]+):([^\"\s]+|\"[^\"]+?\")")
filter_pattern_noncapture = re.compile(r"(?:[^\s]+):(?:[^\"\s]+|\"[^\"]+?\")")
@app.post("/api/search")
async def search(uuid: cookiestr, cohort: cookiestr, query : Annotated[str,Body(...)], bg: BackgroundTasks):
    if len(query)>600:
        await log(uuid,cohort,"error","too long query")
        return JSONResponse(dict(info="Your search query was too long to process."))

    info = ""

    filters = []

    await log(uuid,cohort,"search",query)

    for name,arg in filter_pattern.findall(query):
        if arg.startswith("\""):
            arg = arg[1:-1]

        arg_wildcard_pattern = re.compile(re.escape(arg).replace("\*",".*"))
        # search filters
        if name=="in":
            filters.append(lambda i,arg=arg: app.db[i]["location"].startswith(arg))
        elif name=="-in":
            filters.append(lambda i, arg=arg: not app.db[i]["location"].startswith(arg))
        elif name=="arg":
            filters.append(lambda i, arg=arg_wildcard_pattern: any(arg.fullmatch(x[1]) is not None for x in app.db[i]["args"]))
        elif name=="-arg":
            filters.append(lambda i, arg=arg_wildcard_pattern: not any(arg.fullmatch(x[1]) is not None for x in app.db[i]["args"]))
        else:
            # TODO: HTML escape info.
            info=f"Ignoring invalid filter {name}:\"{arg}\". If you didn't mean for this to be a filter, you can put a space after the colon."

    query = " ".join(filter_pattern_noncapture.split(query)).strip()
   
    if query in app.query_cache:
        scores = app.query_cache[query]
    else:
        score_task = aio.create_task(app.model.run(query))
        done,pending = await aio.wait([score_task],timeout=8)
        if len(pending)==1:
            if app.model.service_lock == 1:
                await log(uuid,cohort,"minor-inconvenience",query)
                r = JSONResponse(dict(results=[],info="We did not have the model loaded at the time of your query. It is loading now, subsequent queries will be fast. Try again in a minute. Sorry!"))
            else:
                await log(uuid,cohort,"severe-inconvenience",query)
                r = JSONResponse(dict(results=[],info="Unfortunately, the (shared) GPU is being used for other purposes. Check back later."))
            bg.add_task(lambda:score_task)
            return r
        scores = await (next(iter(done)))
        app.query_cache[query] = scores
    
    indices = torch.argsort(scores,descending=True)

    results = list(itertools.islice(((i,s) for i,s in zip(indices,scores[indices]) if all(f(i) for f in filters)),100))

    if len(results)>0:
        best_score = results[0][1]
        if best_score < 0.80:
            info = "Your search query seemed difficult or vague to the model. We aren't confident in the results below. The model could be misbehaving or maybe there actually aren't any particularly relevant theorems. You might be able to get better results using tips on the <a href='/help'>help page</a>."
    else:
        info = "There were no results. Maybe you wrote a filter that was too strict?"


    return JSONResponse(dict(results=[app.db[i] | {"score":score.item()} for i,score in results],info=info,docs_available=config.use_docs))

