from fasthtml.common import *
from render_coq import coq_html, find_match

app, rt = fast_app(live=True)

def Fragment(*x):
  return Div(*x, cls="fragment")

def Fragments(*xs):
  return [Fragment(x) for x in xs]

slides = [
  Section(
    H2("The Transfinite Construction"),
    H4("for (well-pointed) endofunctors"),
    r"$1 \to F \to F^2 \to F^3 \to \dots \to F^\omega $"
  ),
  Section(
    Img(src="/diagrams/overview.heic", cls="stretch"),
  ),
  Section(
    Img(src="/diagrams/terminology.heic", cls="stretch"),
  ),
  Section(
    P(r'''
    Let $(F, \sigma : 1 \Rightarrow F)$ be a pointed-endofunctor on $\cat{C}$. We form a chain in $\Fun(\cat{C}, \cat{C})$
    \[1 \xrightarrow{\sigma} F \xrightarrow{F(\sigma)} F^2\xrightarrow{F^2(\sigma)} F^3 \xrightarrow{F^3(\sigma)} \dots \]
    '''),
    Fragment(
      find_match('Notation', 'iter_functor'),
      coq_html['iter_chain_mor'],
    ),
    Fragment(
      P(r'''
      Importantly, there is a "shift" symmetry: $F^{i+1}\sigma = F(F^i\sigma)$.
      '''),
      coq_html['iter_chain_mor_shift'],
    ),
  ),
]

@rt("/")
def get():
  return NotStr("<!DOCTYPE html>"), Html(
    Head(
      Title(r"The Transfinite Construction"),
      Meta(charset="utf-8"),
      Meta(name="viewport", content="width=device-width, initial-scale=1.0, maximum-scale=1.0, user-scalable=no"),
      
      # Reveal.js
      Link(rel="stylesheet", href="/reveal.js/dist/reveal.css"),
      Link(rel="stylesheet", href="/theme.css"),
      Script(src="/reveal.js/dist/reveal.js"),
      Script(src="/reveal.js/plugin/math/math.js"),

      # Chalkboard stuff
      # Link(rel="stylesheet", href="https://cdnjs.cloudflare.com/ajax/libs/font-awesome/6.4.0/css/all.min.css"),
      # Script(src="https://cdnjs.cloudflare.com/ajax/libs/font-awesome/6.4.0/js/all.min.js"),
      # Script(src="/reveal.js-plugins/customcontrols/plugin.js"),
      # Link(rel="stylesheet", href="/reveal.js-plugins/customcontrols/style.css"),
      # Script(src="/reveal.js-plugins/chalkboard/plugin.js"),
      # Link(rel="stylesheet", href="/reveal.js-plugins/chalkboard/style.css"),

      # Custom css
      Link(rel="stylesheet", href="main.css"),
      Link(rel="stylesheet", href="pygments.css"),
      Link(rel="stylesheet", href="alectryon/alectryon/assets/alectryon.css"),
      Link(rel="stylesheet", href="alectryon/alectryon/assets/docutils_basic.css"),
      Script(src="alectryon/alectryon/assets/alectryon.js"),
      Link(rel="stylesheet", href="https://cdnjs.cloudflare.com/ajax/libs/IBM-type/0.5.4/css/ibm-type.min.css", integrity="sha512-sky5cf9Ts6FY1kstGOBHSybfKqdHR41M0Ldb0BjNiv3ifltoQIsg0zIaQ+wwdwgQ0w9vKFW7Js50lxH9vqNSSw==", crossorigin="anonymous"),
      Link(rel="stylesheet", href="https://cdnjs.cloudflare.com/ajax/libs/firacode/5.2.0/fira_code.min.css", integrity="sha512-MbysAYimH1hH2xYzkkMHB6MqxBqfP0megxsCLknbYqHVwXTCg9IqHbk+ZP/vnhO8UEW6PaXAkKe2vQ+SWACxxA==", crossorigin="anonymous"),
    ),
    Body(
      Div(Div(*slides, cls="slides"), cls="reveal"),
      Script(src="init.js"),
    ),
    lang="en",
  )

# @app.get("/{fname:path}.{ext:static}")
# def static_file(fname, ext):
#     return FileResponse(f"{fname}.{ext}")

@app.get("/{path:path}")
def static_file(path: str):
  return FileResponse(path)

@app.get("/favicon.ico")
async def favicon():
  return Response(status_code=204)

serve()