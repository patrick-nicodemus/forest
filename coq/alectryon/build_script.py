import alectryon.pygments

LATEX_START = "⟪"
LATEX_END = "⟫"

class LatexMathFormatter(alectryon.pygments.LatexFormatter):
    def __init__(self, **options):
        options["escapeinside"] = (LATEX_START, LATEX_END) # ← the important setting
        super().__init__(**options)

alectryon.pygments.LatexFormatter = LatexMathFormatter

## Step 2: Create a Pygments filter to turn math ranges into comments
import pygments.filters
import pygments.token

class LatexFilter(pygments.filters.Filter):
    def filter(self, _lexer, stream):
        in_latex = False
        for ttype, value in stream:
            if value == LATEX_START:
                in_latex = True
            if in_latex:
                yield pygments.token.Comment, value
            else:
                yield ttype, value
            if value == LATEX_END:
                in_latex = False

## Step 3: Ask the Coq lexer used by Alectryon to use this new filter
import alectryon.pygments_lexer
class LatexCoqLexer(alectryon.pygments_lexer.CoqLexer):
    def __init__(self, **options):
        options["filters"] = [LatexFilter(), pygments.filters.TokenMergeFilter()] # ← the important setting
        super().__init__(**options)

alectryon.pygments.CUSTOM_LEXERS_BY_ALIAS["coq"] = \
    alectryon.pygments.CUSTOM_LEXERS["CoqLexer"] = \
        LatexCoqLexer

if __name__ == '__main__':
    from alectryon.cli import main
    main()
