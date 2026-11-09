"""Rebuild the four bilingual PDFs from their authoritative Markdown sources."""
from pathlib import Path
import argparse
import json
import os
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
local_tools = Path(os.environ.get('PAPER_TOOLS', '.missing-paper-tools'))
if local_tools.is_dir():
    sys.path.insert(0, str(local_tools))
import pypandoc
import typst
import pymupdf
from PIL import Image, ImageDraw


def render(source, qa_root):
    lang = 'zh' if source.stem.endswith('zh') else 'en'
    algorithm = source.stem.startswith('algorithm-')
    text = source.read_text(encoding='utf-8')
    title = text.splitlines()[0].removeprefix('# ')
    short = (
        '四列重力四子棋 · 统一算法与压缩' if algorithm else '一至四列重力四子棋 · 和棋与最优换列次数'
    ) if lang == 'zh' else (
        'Four-column gravity Connect Four | Uniform algorithm and compression'
        if algorithm else 'Narrow gravity Connect Four | Draw strategies and optimal active budgets'
    )
    # Allow long source identifiers to wrap; leave TeX subscripts untouched.
    text = re.sub(r'\x60([^\x60\n]+)\x60', lambda m: chr(96) + re.sub(r'([./_])', r'\1' + '\u200b', m[1]) + chr(96), text)
    for namespace in ['UniformFour.U1.', 'UniformFour.U2.']:
        text = text.replace(namespace, namespace.replace('.', '.\u200b'))
    text = text.replace('\u2011', '-').replace('\u2013', '-').replace('\u2014', '-')
    result = subprocess.run(
        [pypandoc.get_pandoc_path(), '-f', 'markdown+tex_math_single_backslash', '-t', 'typst'],
        input=text, capture_output=True, text=True, encoding='utf-8', check=True)
    header = r'''
#set document(title: TITLE, author: "GPT",
    date: datetime(year: 2026, month: 11, day: 8))
#set page(paper: "a4", margin: (x: 22mm, top: 21mm, bottom: 21mm),
    numbering: "1", number-align: center,
    header: context {
      if counter(page).get().first() > 1 {
        text(size: 7.5pt, fill: rgb("#666666"))[SHORT]
        v(2pt)
        line(length: 100%, stroke: 0.35pt + rgb("#b0b0b0"))
      }
    })
#set text(font: ("Times New Roman", "Liberation Serif", "SimSun", "Noto Serif CJK SC"), size: 10.5pt, lang: LANG)
#set par(justify: true, leading: 0.56em, spacing: 0.65em)
#set heading(outlined: true)
#show heading.where(level: 1): it => block(above: 0pt, below: 12pt)[
  #align(center, text(font: ("Times New Roman", "Liberation Serif", "Microsoft YaHei", "Noto Sans CJK SC"), size: 20pt, weight: "bold", hyphenate: false, it.body))
]
#show heading.where(level: 2): it => block(above: 15pt, below: 8pt, sticky: true)[
  #text(font: ("Times New Roman", "Liberation Serif", "Microsoft YaHei", "Noto Sans CJK SC"), size: 13.5pt, weight: "bold", it.body)
]
#show heading.where(level: 3): it => block(above: 10pt, below: 5pt, sticky: true)[
  #text(font: ("Times New Roman", "Liberation Serif", "Microsoft YaHei", "Noto Sans CJK SC"), size: 11.5pt, weight: "bold", it.body)
]
#show link: set text(fill: rgb("#244f6b"))
#set table(inset: 5pt, stroke: 0.35pt + rgb("#aab3bc"))
#show table: set text(size: 8.5pt)
#show raw: set text(font: ("Consolas", "DejaVu Sans Mono", "SimSun", "Noto Serif CJK SC"), size: 8.6pt)
'''
    header = header.replace('TITLE', json.dumps(title, ensure_ascii=False))
    header = header.replace('SHORT', short).replace('LANG', json.dumps(lang))
    body = result.stdout
    # Pandoc maps TeX varnothing to a diameter symbol; use the actual empty set.
    body = re.sub(r'\bdiameter\b', 'emptyset', body)
    body = re.sub(r'\nGPT\n\n([^\n]+)\n\n',
                  lambda m: '\n#align(center)[GPT #linebreak() ' + m[1] + ']\n\n',
                  body, count=1)
    if not algorithm:
        body = re.sub(r'^== ([^\n]+)\n<[^>]+>\n',
                      lambda m: '#align(center)[#text(size: 12pt, weight: "bold")[' + m[1] + ']]\n',
                      body, count=1, flags=re.M)
    for heading in ['== 参考文献', '== References']:
        if heading in body:
            before, refs = body.split(heading, 1)
            body = before + '#block(breakable: false)[\n' + heading + refs + '\n]\n'
    target = source.with_suffix('.typ')
    target.write_text((header + '\n' + body).rstrip() + '\n', encoding='utf-8', newline='\n')
    pdf = source.with_suffix('.pdf')
    typst.compile(str(target), output=str(pdf), font_paths=[os.environ.get('PAPER_FONTS','C:/Windows/Fonts')] if Path(os.environ.get('PAPER_FONTS','C:/Windows/Fonts')).is_dir() else [])
    # Also supply editable LaTeX source, without claiming it generated this PDF.
    latex = subprocess.run(
        [pypandoc.get_pandoc_path(), '-f', 'markdown+tex_math_single_backslash', '-t', 'latex', '-s',
         '-V', 'documentclass=article', '-V', 'papersize=a4', '-V', 'geometry:margin=22mm',
         '-V', 'mainfont=Times New Roman', '-V', 'CJKmainfont=SimSun', '-V', 'author=GPT'],
        input=source.read_text(encoding='utf-8'), capture_output=True, text=True, encoding='utf-8', check=True)
    source.with_suffix('.tex').write_text(latex.stdout.rstrip() + '\n', encoding='utf-8', newline='\n')
    doc = pymupdf.open(pdf)
    qadir = qa_root / (('algorithm_' if algorithm else 'mathematics_') + lang)
    qadir.mkdir(parents=True, exist_ok=True)
    pages, errors = [], []
    thumbs = []
    for n, page in enumerate(doc, 1):
        raw = page.get_text()
        if '\ufffd' in raw:
            errors.append(f'page {n}: replacement glyph')
        for b in page.get_text('dict')['blocks']:
            for line in b.get('lines', []):
                for span in line['spans']:
                    if not span['text'].strip():
                        continue
                    x0,y0,x1,y1 = span['bbox']
                    if x0 < 35 or x1 > page.rect.width - 35 or y0 < 10 or y1 > page.rect.height - 10:
                        errors.append(f'page {n}: outside safe page area: {span["text"][:60]}')
        pix = page.get_pixmap(matrix=pymupdf.Matrix(1.4, 1.4))
        filename = qadir / f'page-{n:02}.png'
        pix.save(filename)
        thumb = Image.open(filename).convert('RGB')
        thumb.thumbnail((298, 422))
        tile = Image.new('RGB', (316, 450), 'white')
        tile.paste(thumb, ((316-thumb.width)//2, 5))
        ImageDraw.Draw(tile).text((12,430), f'{qadir.name} p{n}', fill='black')
        thumbs.append(tile)
        pages.append({'page':n, 'characters':len(raw)})
    for start in range(0, len(thumbs), 6):
        batch=thumbs[start:start+6]
        sheet=Image.new('RGB',(316*3,450*2),'#ddd')
        for i,tile in enumerate(batch):
            sheet.paste(tile,((i%3)*316,(i//3)*450))
        sheet.save(qadir/f'contact-{start//6+1:02}.png')
    report = {
        'pdf': pdf.name, 'title':title, 'author':doc.metadata.get('author'),
        'pages':pages, 'automated_layout_errors':errors,
        'pandoc':str(pypandoc.get_pandoc_version()), 'typst':typst.__version__,
        'warnings':result.stderr, 'render_engine':'Typst; .tex is a separate editable export',
        'qa_images':qadir.relative_to(qa_root).as_posix(),
    }
    (qadir/'render-report.json').write_text(json.dumps(report,ensure_ascii=False,indent=2),encoding='utf-8')
    print(json.dumps({'paper':str(source.relative_to(ROOT)), 'pages':len(doc), 'errors':errors,
                      'warnings':result.stderr, 'author':doc.metadata.get('author')},ensure_ascii=False), flush=True)
    assert not errors
    assert doc.metadata.get('author') == 'GPT'
    doc.close()


if __name__ == '__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--only', default='')
    parser.add_argument('--qa', type=Path, default=ROOT/'papers/render-qa')
    args=parser.parse_args()
    for source in sorted((ROOT/'papers').glob('*-*.md')):
        if args.only and args.only not in str(source):
            continue
        render(source,args.qa)
