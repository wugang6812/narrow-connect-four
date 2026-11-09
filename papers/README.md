# Papers and editable sources

| Subject | English | Chinese |
|---|---|---|
| Draw strategies and optimal active budgets | [PDF](paper-en.pdf), [Markdown](paper-en.md) | [PDF](paper-zh.pdf), [Markdown](paper-zh.md) |
| Uniform algorithm and compression | [PDF](algorithm-en.pdf), [Markdown](algorithm-en.md) | [PDF](algorithm-zh.pdf), [Markdown](algorithm-zh.md) |

Markdown is the editorial source. PDFs use Pandoc 3.9 and Typst 0.15.0 through
[render_papers.py](../tools/render_papers.py). Each manuscript includes a .typ
typesetting source and a .tex editable export. The LaTeX export did not generate
the delivered PDF.

Install pypandoc_binary, typst, PyMuPDF and Pillow, then run
python tools/render_papers.py. Fonts: Times New Roman and SimSun/Microsoft YaHei,
or the supported Liberation/Noto CJK fallbacks. PAPER_FONTS selects a font
directory; PAPER_TOOLS optionally selects a Python dependency directory.
The original rendering used Windows fonts; font changes can alter pagination.
Page images and render reports stay in the ignored papers/render-qa directory.

Optimality and its full mathematical proofs are in the first paper. The second
develops the uniform algorithm and compression. Each states its formal scope.
See [references.bib](references.bib) for external works and both paper citations,
and [LICENSE.txt](LICENSE.txt) for CC BY 4.0.
