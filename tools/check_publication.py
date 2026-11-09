"""Check current paper bytes and links without network or optional packages."""
from pathlib import Path
from html.parser import HTMLParser
from urllib.parse import unquote, urlsplit
import hashlib
import json
import re

ROOT=Path(__file__).resolve().parents[1]
REPO_PREFIX='https://github.com/wugang6812/narrow-connect-four/'


class Links(HTMLParser):
    def __init__(self):
        super().__init__()
        self.links=[]
    def handle_starttag(self,tag,attrs):
        for key,value in attrs:
            if key in {'href','src'} and value:
                self.links.append(value)


def target_path(source,link):
    if link.startswith(REPO_PREFIX):
        tail=link[len(REPO_PREFIX):]
        for prefix in ['blob/main/','tree/main/']:
            if tail.startswith(prefix):
                return ROOT/unquote(urlsplit(tail[len(prefix):]).path)
        return None
    parsed=urlsplit(link)
    if parsed.scheme or parsed.netloc or not parsed.path:
        return None
    path=unquote(parsed.path)
    return (ROOT/path.lstrip('/') if path.startswith('/') else source.parent/path).resolve()


def main():
    manifest=json.loads((ROOT/'audit/paper-manifest.json').read_text(encoding='utf-8'))
    assert len(manifest['papers'])==4
    paper_files=[]
    for paper in manifest['papers']:
        assert paper['author']=='GPT' and paper['pages']>0
        for entry in paper['files']:
            path=ROOT/entry['path']
            assert hashlib.sha256(path.read_bytes()).hexdigest()==entry['sha256'],entry['path']
            paper_files.append(path)
        pdf=next(ROOT/x['path'] for x in paper['files'] if x['path'].endswith('.pdf'))
        assert pdf.read_bytes().startswith(b'%PDF-')
    expected={f'{stem}-{lang}{ext}' for stem in ['paper','algorithm']
              for lang in ['en','zh'] for ext in ['.md','.pdf','.typ','.tex']}
    assert {p.name for p in paper_files}==expected
    assert json.loads((ROOT/'package.json').read_text())['version']=='0.2.0'
    sources=[ROOT/'README.md',ROOT/'README.zh-CN.md',ROOT/'index.html',ROOT/'game/index.html',
             ROOT/'THIRD_PARTY.md',ROOT/'papers/README.md']
    sources+=list((ROOT/'docs').glob('*.md'))
    sources+=[ROOT/'proof/README.md',ROOT/'proof/Covering/README.md',ROOT/'proof/Narrow/README.md']
    sources+=[p for p in paper_files if p.suffix=='.md']
    count=0
    for source in sources:
        content=source.read_text(encoding='utf-8')
        if source.suffix=='.html':
            parser=Links();parser.feed(content);links=parser.links
        else:
            links=[a or b for a,b in re.findall(r'\[[^\]\n]*\]\((?:<([^>]+)>|([^\s)]+))\)',content)]
        for link in links:
            target=target_path(source,link)
            if target is not None:
                assert target.resolve().is_relative_to(ROOT.resolve()),('Outside repository',source.name,link)
                assert target.exists(),('Broken link',source.relative_to(ROOT).as_posix(),link)
                count+=1
    print(json.dumps({'status':'passed','papers':4,'manuscript_artifacts':len(paper_files),
                      'checked_local_links':count,'scope':'Published bytes and local navigation; no remote-URL or mathematical validation.'}))


if __name__=='__main__':
    main()
