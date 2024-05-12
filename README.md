# ProofDB User Interface

**Notice: This service expects to be used in conjunction with a reasonably good NVIDIA GPU. If you don't have one, why not try our [live demo?](https://proofdb.tompreichel.com/)?**

This repo hosts the user interface for a natural language Coq theorem search engine.

# Installation

Clone this repo.

Run `pip install -r requirements.txt` (preferably in a virtualenv) to install dependencies.

Download the model *before* running the server by running the following python snippet:
```python
import transformers
model = transformers.AutoModel.from_pretrained("EleutherAI/llemma_7b")
model.load_adapter("tomreichel/proofdb-HN")
```
If you don't do this step, it'll try to download it the first time the model is loaded, which is the first time a search is sent. Then you'll have to wait several minutes while the model downloads and the search will time out, which can cause confusing things to happen!

We will release instructions to generate databases for custom selections of Coq packages, but in the meantime download [this zip file](https://tompreichel.com/proofdb-builds/db.8.18.zip).
It contains a prebuilt database for ~90,000 theorems in the Coq 8.18 release of [Coq Platform](https://github.com/coq/platform).
Unzip it into the repo, which should create a `doc` folder and a `db` folder.

The `doc` folder contains coqdocs generated for the theorems in the database, while the `db` folder contains theorem metadata (`theorems.json`), embeddings (`vecs.pt`), an sqlite database for logging user interactions (`log.db`), and a random projection to facilitate binary vector encoding (`projection.pt`).

Check `config.py` and adjust settings according to your preferences.

Start the server using `uvicorn main:app` in the repo directory. The port the service is running on will be printed to console. You can navigate to `localhost:<port number>` in your browser to view the service.

The first time you query the server it will load the embedding model into memory. This will take some time, and it will not return results (it will repeat the same information I have given you and tell you to retry), but subsequent queries will work and be faster.
