from pygments.lexer import RegexLexer, words
from pygments.token import *

# very rough lexer; not 100% precise
class CustomLexer(RegexLexer):
    name = 'Vale'
    aliases = ['vale']
    filenames = ['*.vad', '*.vaf']
    keywords = (
        'Type',
        'type',
        'Dependent',
        'dependent',
        'const',
        'readonly',
        'function',
        'returns',
        'axiom',
        'extern',
        'procedure',
        'lets',
        'requires',
        'ensures',
        'reads',
        'modifies',
        'preserves',
        'decreases',
        'invariant',
        'assert',
        'implies',
        'by',
        'assume',
        'calc',
        'havoc',
        'goto',
        'lemma',
        'call',
        'forall',
        'exists',
        'fun',
        'old',
        'this',
        'true',
        'false',
        'is',
        'let',
        'in',
        'out',
        'inout',
        'var',
        'if',
        'then',
        'else',
        'while',
        'for',
        'return',
        'reveal',
        'static',
        'module',
        'import',
        'ghost',
        'inline',
        'operator',
        'include',
        'operand_type',
        'tuple',
        'bool',
        'prop',
        'int',
        'int_range',
    )
    tokens = {
        'root': [
            (r' ', Text),
            (r'\n', Text),
            (r'\r', Text),
            (r'//.*\n', Comment),
            (r'/[*]([^*]|[*]+[^/])*[*]+/', Comment),
            (words(keywords, suffix=r'\b'), Keyword),
            (r'0x[0-9a-fA-F_]+', Literal.Number),
            (r'[0-9_]+', Literal.Number),
            (r'[a-zA-Z_]+', Text),
            (r'.', Text),
        ]
    }

#class CustomFormatter:


