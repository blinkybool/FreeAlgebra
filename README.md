# FreeAlgebra

A (UniMath) formalization in Coq of the transfinite construction of the free algebra on a (well-) (pointed-) endofunctor.

## Source Material
- [Max Kelly, A unified treatment of transfinite constructions for free algebras, free monoids, colimits, associated sheaves, and so on](https://www.cambridge.org/core/journals/bulletin-of-the-australian-mathematical-society/article/unified-treatment-of-transfinite-constructions-for-free-algebras-free-monoids-colimits-associated-sheaves-and-so-on/FE2E25E4959E4D8B4DE721718E7F55EE)
- [nlab, transfinite construction of free algebras](https://ncatlab.org/nlab/show/transfinite+construction+of+free+algebras)

## Limitations
- We consider only the case \Kappa=ℕ wherever cardinality is relevant. TODO: explain consequences of this.

## Build presentation

```bash
# Pull the submodules (reveal.js for slides and alectryon to render coq to interactive html)
git submodule update --init --recursive
# install fastHTML (inside a virtual env if you like)
pip install python-fasthtml
# Run the fastHMTL server
cd presentation
python app.py
# Open it in your browser
open http://localhost:5001
```