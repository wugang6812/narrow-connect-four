"""Smoke and interaction tests against the real offline browser UI."""
from pathlib import Path
from datetime import datetime
import argparse
import json
import tempfile
from playwright.sync_api import sync_playwright

ROOT=Path(__file__).resolve().parents[1]
parser=argparse.ArgumentParser()
parser.add_argument('--browser',default=r'C:\Program Files\Google\Chrome\Application\chrome.exe')
args=parser.parse_args()
checks=[]

with sync_playwright() as p:
    browser=p.chromium.launch(executable_path=args.browser,headless=True)
    context=browser.new_context(viewport={'width':1280,'height':1024},accept_downloads=True)
    page=context.new_page();errors=[]
    page.on('pageerror',lambda e:errors.append(str(e)))
    page.goto((ROOT/'game/index.html').as_uri())
    page.wait_for_selector('#column-buttons button')

    def count():return page.locator('.disc').count()
    def click(c):page.locator(f'#column-buttons [data-column="{c}"]').click()
    def setup(r,c,mode='two',human=1):
        page.locator('#rows').fill(str(r));page.locator('#columns').fill(str(c))
        page.locator('#mode').select_option(mode)
        if mode=='computer':page.locator('#human').select_option(str(human))
        page.locator('#new-game').click()

    assert page.locator('.cell').count()==42
    click(0);click(0)
    assert page.locator('.cell[data-column="0"][data-row="0"] .black').count()==1
    assert page.locator('.cell[data-column="0"][data-row="1"] .white').count()==1
    checks.append('offline loading, gravity and alternating colors')
    page.locator('#undo').click();assert count()==1
    page.locator('#restart').click();assert count()==0
    for c in [0,0,1,1,2,2,3]:click(c)
    assert page.locator('.win').count()==4
    assert '获胜' in page.locator('#status').inner_text()
    assert page.locator('#column-buttons button:enabled').count()==0
    page.locator('#board .cell').first.click();assert count()==7
    page.locator('#undo').click();assert count()==6
    checks.append('win highlights, terminal guard and undoing a win')
    setup(1,1);click(0);assert '和棋' in page.locator('#status').inner_text()
    setup(2,3);click(0);click(0)
    assert page.locator('#column-buttons [data-column="0"]').is_disabled()
    page.locator('.cell[data-column="0"]').first.click();assert count()==2
    assert '已满' in page.locator('#notice').inner_text()
    checks.append('one-cell draw and full-column rejection')
    setup(6,7)
    page.locator('#rows').fill('21');page.locator('#new-game').click()
    assert page.locator('.cell').count()==42;assert '整数' in page.locator('#notice').inner_text()
    setup(20,20);assert page.locator('.cell').count()==400
    click(19);assert page.locator('.cell[data-column="19"][data-row="0"] .black').count()==1
    checks.append('size validation and a 20 by 20 board')
    setup(6,4);assert '最优策略' in page.locator('#research-title').inner_text()
    page.locator('#language').click();assert page.locator('html').get_attribute('lang')=='en'
    assert 'optimal' in page.locator('#research-title').inner_text()
    page.reload();assert page.locator('html').get_attribute('lang')=='en'
    setup(6,7);assert 'wider than four' in page.locator('#research-description').inner_text()
    checks.append('bilingual UI, language persistence and theorem scope')
    click(0);click(1);page.reload();assert count()==2
    with page.expect_download() as download_event:page.locator('#export').click()
    with tempfile.TemporaryDirectory() as tmp:
        exported=Path(tmp)/'record.json';download_event.value.save_as(exported)
        assert json.loads(exported.read_text())['moves']==[1,2]
        setup(1,1)
        page.locator('#record-file').set_input_files(str(exported))
        page.wait_for_function('document.querySelectorAll(".disc").length===2')
        assert page.locator('.cell').count()==42
        exported.write_text(json.dumps({'format':'gravity-connect-four','version':1,'rows':1,'columns':1,'moves':[1,1]}))
        page.locator('#record-file').set_input_files(str(exported))
        page.wait_for_function('document.querySelector("#notice").textContent.startsWith("Invalid record")')
        assert count()==2
    checks.append('saved game reload, export/import round trip and illegal record rejection')
    setup(6,7,'computer',1);click(0)
    page.wait_for_function('document.querySelectorAll(".disc").length===2')
    page.locator('#undo').click();assert count()==0
    click(1);page.locator('#restart').click()
    page.wait_for_timeout(600);assert count()==0
    assert 'backup move' not in page.locator('#notice').inner_text()
    checks.append('C computer, two-ply undo and cancelling a pending computer move')
    setup(6,7,'computer',2)
    page.wait_for_function('document.querySelectorAll(".disc").length===1')
    assert page.locator('#undo').is_disabled()
    assert 'White' in page.locator('#status').inner_text()
    checks.append('computer moves first when human selects White')
    # Regression for the reported bug: selecting Computer applies without New Game.
    setup(6,7);click(0)
    page.locator('#mode').select_option('computer')
    page.locator('#human').select_option('1')
    page.wait_for_function('document.querySelectorAll(".disc").length===2')
    assert 'backup' not in page.locator('#notice').inner_text()
    checks.append('computer mode takes effect immediately, without restarting the board')
    setup(6,7,'computer',2)
    page.locator('#difficulty').select_option('3')
    page.wait_for_function('document.querySelectorAll(".disc").length===1')
    assert 'accepted first-player' in page.locator('#notice').inner_text()
    click(0)
    page.wait_for_function('document.querySelectorAll(".disc").length===3',timeout=60000)
    assert 'accepted first-player' in page.locator('#notice').inner_text()
    page.locator('#mode').select_option('two')
    checks.append('super-hard policy loads offline and the C worker follows the first-player certificate')
    setup(6,7);page.locator('body').click(position={'x':4,'y':4})
    selected=int(page.locator('#column-buttons button.selected').get_attribute('data-column'))
    page.keyboard.press('ArrowRight');page.keyboard.press('Space');assert count()==1
    assert page.locator(f'.cell[data-column="{(selected+1)%7}"][data-row="0"] .black').count()==1
    checks.append('keyboard selection and dropping')
    setup(20,20);page.set_viewport_size({'width':390,'height':844})
    assert page.evaluate('document.documentElement.scrollWidth<=innerWidth')
    assert page.locator('#board-scroll').evaluate('(e)=>e.scrollWidth>e.clientWidth')
    (ROOT/'audit').mkdir(exist_ok=True)
    page.screenshot(path=str(ROOT/'audit/game-mobile.png'),full_page=True)
    setup(6,7);page.set_viewport_size({'width':1280,'height':1024})
    page.locator('#language').click()
    page.screenshot(path=str(ROOT/'audit/game-desktop.png'),full_page=True)
    checks.append('mobile large-board scrolling with no page overflow')
    assert not errors,errors
    receipt={'status':'passed','checked_at':datetime.now().astimezone().isoformat(),
             'browser':'Chromium via Playwright','checks':checks,'javascript_errors':errors,
             'scope':'Browser game only, not a Lean proof audit.'}
    (ROOT/'audit/browser-tests.json').write_text(json.dumps(receipt,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(receipt,ensure_ascii=False,indent=2))
    browser.close()
