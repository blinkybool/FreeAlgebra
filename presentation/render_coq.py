import alectryon.serapi
import alectryon.transforms
from alectryon.transforms import IOAnnots
from alectryon.core import Hypothesis, Goal, Message, Sentence, Text, RichSentence, RichCode, RichHypothesis, RichGoal, RichMessage, Messages, Goals
from alectryon.html import HtmlGenerator
from alectryon.pygments import make_highlighter

def split_sections(input, is_start, is_end):
  current = None
  output = []
  for x in input:

    if current is None and is_start(x):
      assert current is None
      current = []
    if current is not None:
      current.append(x)

      if is_end(x):
        output.append(current)
        current = None

  if current is not None and len(current) > 0:
    output.append(current)
  return output

def start_of_decl(x):
  return isinstance(x, RichSentence)

def end_of_decl(x):
  if not isinstance(x, RichSentence):
    return False
  c = x.input.contents.strip()
  messages, goals = x.outputs
  return c[0].isupper() and len(goals.goals) == 0

def extract_ident(decl):
  first = decl[0]
  words = first.input.contents.split()
  if len(words) == 0:
    return first.input.contents
  if words[0] in {"Definition", "Theorem", "Lemma"}:
    return words[1]
  return first.input.contents

def gen_decl_dict(decls):
  lookup = {}
  for decl in decls:
    ident = extract_ident(decl)
    if ident is None:
      lookup[decl[0].input.contents] = decl
    else:
      lookup[ident] = decl

  return lookup

def gen_html_dict(decl_dict, html_generator):
  
  return {
    ident: html_generator.gen_fragments(decl)
    for ident, decl in decl_dict.items()
  }

def format_decl(decl):
  return (
    '(*' + ('-'* 40) + '*)\n'
    + '\n'.join(x.input.contents if isinstance(x, RichSentence) else x.contents for x in decl)
    # + '(*' + ('-'* 40) + '*)'
  )

with open("../well_pointed_algebras.v", 'r') as f:
  content = f.read()

fragments = alectryon.serapi.annotate([content])[0]
transformed = alectryon.transforms.default_transform(fragments, 'coq')

decls = split_sections(transformed, start_of_decl, end_of_decl)

highlighter = make_highlighter("html", "coq", "default")
html_generator = HtmlGenerator(highlighter, minify=False)

decl_dict = gen_decl_dict(decls)
coq_html = gen_html_dict(decl_dict, html_generator)

def find_match(*keywords):
  for ident, html in coq_html.items():
    if all(keyword in ident for keyword in keywords):
      return html
  return f"FAIL ({','.join(keywords)})"