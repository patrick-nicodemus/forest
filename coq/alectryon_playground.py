from alectryon import cli
parser = cli.build_parser()

# These are the default steps in the pipeline, associated to this input (frontend) and output (backend)
# pipelines=
#   [('A.v', 'coq+rst', 'latex',
#    (<function read_plain at 0x78716e4dc360>,
#     <function register_docutils at 0x78716e109440>,
#     <function gen_docutils at 0x78716e109620>,
#     <function copy_assets at 0x78716e109d00>,
#     <function write_file.<locals>.<lambda> at 0x78716e10ae80>
#   ))])

# read_plain just literally reads the text as a utf-8 string with no parsing.
# register_docutils sets some initial settings.
# gen_docutils does a lot of actual work, so let's dive in there.

# Args: Namespace(
#   input=['A.v'],
#   stdin_filename=None,
#   frontend='coq+rst',
#   coq_driver='sertop',
#   backend='latex',
#   output='latex/A.tex',
#   output_directory=None,
#   copy_fn=<function copyfile at 0x743c5d856c00>,
#   pygments_style=None,
#   mark_point=(None, None),
#   include_banner='True',
#   include_vernums=True,
#   cache_directory=None,
#   cache_compression=None,
#   webpage_style='centered',
#   html_minification=False,
#   html_dialect='html4',
#   latex_dialect='pdflatex',
#   sertop_args=[],
#   coqc_args=[],
#   coq_args_I=[],
#   coq_args_Q=[],
#   coq_args_R=[],
#   leanInk_args_lake=None,
#   long_line_threshold=72, expect_unexpected=False, debug=False, traceback=False, backend_dialects={'webpage': 'html4', 'latex': 'pdflatex'}, language_drivers={'coq': 'sertop', 'lean3': 'lean3_repl', 'lean4': 'leanInk'}, driver_args_by_name={'sertop': [], 'sertop_noexec': [], 'coqc_time': [], 'lean3_repl': (), 'leanInk': []}, point=None, marker=None,
#   pipelines=[('A.v', 'coq+rst', 'latex', (<function read_plain at 0x743c5dadc360>, <function register_docutils at 0x743c5d73d440>, <function gen_docutils at 0x743c5d73d620>, <function copy_assets at 0x743c5d73dd00>, <function write_file.<locals>.<lambda> at 0x743c5d73ee80>))])


def gen_docutils(src, frontend, backend, fpath, dialect,
                 docutils_settings_overrides, assets, exit_code):
    from .docutils import get_pipeline, alectryon_state
    # get_pipeline is defined in the alectryon.docutils module
    # read the comment at the top of the file.
    pipeline = get_pipeline(frontend, backend, dialect)
    text, pub, exit_code.val = \
        _gen_docutils(src, fpath,
                      pipeline.parser, pipeline.reader, pipeline.writer,
                      docutils_settings_overrides)

    embedded_assets = alectryon_state(pub.document).embedded_assets
    _record_assets(assets,
                   pipeline.translator.ASSETS_PATH,
                   [a for a in pipeline.translator.ASSETS if a not in embedded_assets])

    return text

# get_pipeline calls get_reader, get_parser, and get_writer, which
# returns a translator and a writer.

# For us, reader = StandaloneReader
# get_parser returns RSTCoqParser
# get_writer returns BACKENDS =     'latex': {
# 'pdflatex': (LatexTranslator, LatexWriter),
# 'xelatex': (XeLatexTranslator, XeLatexWriter),
# 'lualatex': (LuaLatexTranslator, LuaLatexWriter),
# now we construct Pipeline(StandaloneReader, RSTCoqParser, LatexTranslator, LatexWriter)
# LatexWriter is built from latex2e.Writer and LatexTranslator
# LatexTranslator = make_LatexTranslator(latex2e.LaTeXTranslator)

# Okay. So, it seems like the "XML" objects that are returned by the parser can contain
# - arbitrary Python objects with internal state
# - dummy nodes corresponding to XML values yet to be computed by Python.
# Our conclusion is that the RSTLiterateParser does _do_ something.
# It strips all the Coq code out of the source tree and replaces it with dummy nodes,
# and returns a "rich XML tree" containing a Python object.

# Trying to go through this again because I feel like I'm missing something.
# First, we build the parser, using user input as help.
# I really don't think this does anything but collect the things I said earlier.
# Then we run post_process_arguments which ... does kind of do a lot?
# No, I still don't think so.

# What is the setup with register_docutils?
# - It sets a bunch of parameters which are probably not useless.
# 

# Here is something subtle.
# The parse function in RSTLiterateParser calls:
#         alectryon_state(document).root_is_code = True
# which does:

st = document.get("alectryon_state")
    if st is None:
        st = document["alectryon_state"] = AlectryonState(document)
    return st
# So, that's where we bring this AlectryonState constructor into it.

# Okay, I'm getting closer. There's an "applytransforms" method.
# I'm stepping through the interactive playback and running the parse function
# so I can see what happens.

# Now we are getting somewhere. The state machine runs a regex on each line of the file
# and uses it to match it to a certain action.
# On line 2, where we have an implicit .. coq:: directive (in the .rst version at least)
# the regex searches for ".. *:" and then tries to match the * to some known directive.
# ".. coq::" is an example of what is called "explicit markup"
# and the function which searches for what this does is called "ExplicitConstruct".
# self.explicit.constructs contains both the regexes that trigger the construct,
# and the parser triggered by that construct (?)
# Then we call the directive function
# docutils/parsers/rst/states.py(2105)directive()

2099 	    def directive(self, match, **option_presets):
2100 	        """Returns a 2-tuple: list of nodes, and a "blank finish" boolean."""
2101 	        type_name = match.group(1)
2102 	        directive_class, messages = directives.directive(
2103 	            type_name, self.memo.language, self.document)
2104 	        self.parent += messages
2105 ->	        if directive_class:
2106 	            return self.run_directive(
2107 	                directive_class, match, type_name, option_presets)
2108 	        else:
2109 	            return self.unknown_directive(type_name)

Here it found the directive_class <alectryon.docutils.CoqDirective>, i'm not sure how that got attached
but it seems pretty easy to configure that.

type_name is coq.

Now, we can instantiate and run the instance of the directive class, in alectryon/docutils.
And _that's_ the function that instantiates the "pending" class and attaches it to the document,
namely in the directive.run() method.

So that gives a few couple questions:
- What's the mechanism that ties ".. coq::" to alectron.docutils.CoqDirective. That's probably in the config settings
- Okay, apparently alectron.docutils.CoqDirective isn't a real thing in the source code.
- That's super confusing.
- What the directive actually is is alectron.docutils.ProverDirective.
- What does the pending method do?

...

Okay, I'm looking at this again.
I just directly inspect the LatexGeneration code.

We have the function

  def gen_code(self, code):
        with Concat(*self.highlight_enriched(code)) as block:
            print(block)
            self.gen_mrefs(code)
            return block

which calls self.highlight_enriched (defined in core)

def highlight_enriched(self, obj):
        lang = obj.props.get("lang")
        with self.highlighter.override(lang=lang) if lang else nullctx():
            return self.highlight(obj.contents)

