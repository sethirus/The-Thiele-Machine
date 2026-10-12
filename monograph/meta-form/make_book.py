#!/usr/bin/env python3
"""A conserved body of words, undergoing the operations it describes.

Copyright 2026 Devon Thiele. CC-BY-SA-4.0.
The released manuscript is read, never modified.
"""
from pathlib import Path
import hashlib
import json
import math
import re
import subprocess

import fitz
import numpy as np

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
REV = 'e4c234627651f1b12eb649148a051d5a252ed6b4'
W, H = 540, 720
INK = (.065, .060, .055)
PAPER = (1, 1, 1)
FONTROOT = Path('/usr/share/fonts/opentype/urw-base35')
PATHS = {'body': FONTROOT/'P052-Roman.otf',
         'italic': FONTROOT/'P052-Italic.otf',
         'display': FONTROOT/'NimbusRoman-Regular.otf',
         'displayitalic': FONTROOT/'NimbusRoman-Italic.otf',
         'sans': FONTROOT/'NimbusSans-Regular.otf'}
FONTS = {k:fitz.Font(fontfile=str(p)) for k,p in PATHS.items()}
SRC = subprocess.check_output(['git','show',REV+':monograph/monograph.tex'],cwd=ROOT,text=True)
PARA = next(p.strip() for p in re.split(r'\n\s*\n',SRC) if p.startswith('A word on what I actually do,'))
assert '\\' not in PARA
PARA = re.sub(r'\s+',' ',PARA)
WORDS = PARA.split()
IDS = list(range(len(WORDS)))
doc = fitz.open()
log = []
CURRENT = []
MODE = None

def width(s,size,font='body'):
    return FONTS[font].text_length(s,fontsize=size)

def raw(p,x,y,s,size=12,font='body',color=INK,angle=0):
    p.insert_font(fontname=font,fontfile=str(PATHS[font]))
    point=fitz.Point(x,y)
    p.insert_text(point,s,fontsize=size,fontname=font,color=color,
                  morph=(point,fitz.Matrix(angle)) if angle else None)

def put(p,i,x,y,size=12,font='body',angle=0,color=INK):
    raw(p,x,y,WORDS[i],size,font,color,angle)
    CURRENT.append({'id':i,'word':WORDS[i],'x':float(x),'y':float(y),
                    'size':float(size),'font':font,'angle':float(angle)})

def page(mode=None):
    global CURRENT,MODE
    if MODE is not None:
        assert sorted(t['id'] for t in CURRENT)==IDS, (MODE, sorted(set(IDS)-{t['id'] for t in CURRENT}))
        log.append({'page':len(doc),'operation':MODE,'words':CURRENT})
    CURRENT=[]
    MODE=mode
    return doc.new_page(width=W,height=H)

def finish():
    global MODE
    if MODE is not None:
        assert sorted(t['id'] for t in CURRENT)==IDS
        log.append({'page':len(doc),'operation':MODE,'words':CURRENT})
        MODE=None

def phrase(s):
    target=s.split()
    for i in IDS:
        if WORDS[i:i+len(target)]==target:return list(range(i,i+len(target)))
    raise ValueError(s)

def without(chosen):
    return [i for i in IDS if i not in set(chosen)]

def flow(p,ids,x,y,w,size=12,leading=None,font='body',bottom=675):
    leading=leading or size*1.45
    left=x
    for i in ids:
        advance=width(WORDS[i],size,font)
        if x+advance>left+w:
            x,y=left,y+leading
        assert y<=bottom,(MODE,WORDS[i],y,bottom)
        put(p,i,x,y,size,font)
        x+=advance+width(' ',size,font)
    return y

def regular(p):
    flow(p,IDS,69,157,401,14.2,20.8,bottom=666)

def mask_of(p):
    pix=p.get_pixmap(matrix=fitz.Matrix(1,1),colorspace=fitz.csGRAY,alpha=False)
    a=np.frombuffer(pix.samples,np.uint8).reshape(H,W)<245
    out=a.copy()
    for dy in range(-3,4):
        for dx in range(-3,4):
            y0,y1=max(0,dy),min(H,H+dy)
            x0,x1=max(0,dx),min(W,W+dx)
            out[y0:y1,x0:x1]|=a[y0-dy:y1-dy,x0-dx:x1-dx]
    return out

def flow_around(p,ids,size=10,top=65,bottom=660):
    mask=mask_of(p)
    while size>=9:
        n=0
        places=[]
        for y in np.arange(top,bottom,size*1.5):
            row=mask[max(0,int(y-size*.84)):min(H,int(y+size*.32)+1)].any(axis=0)
            spans=[]
            start=None
            for x in range(38,503):
                if not row[x] and start is None:start=x
                if (row[x] or x==502) and start is not None:
                    end=x if row[x] else x+1
                    if end-start>30:spans.append((start,end))
                    start=None
            for a,b in spans:
                x=float(a)
                while n<len(ids):
                    i=ids[n]
                    adv=width(WORDS[i],size)
                    if x+adv>b:break
                    places.append((i,x,float(y),size))
                    x+=adv+width(' ',size)
                    n+=1
            if n==len(ids):break
        if n==len(ids):
            for i,x,y,sz in places:put(p,i,x,y,sz)
            return
        size-=.1
    raise AssertionError((MODE,n,len(ids)))

# Cover. The conserved sequence begins on the following page.
p=page()
raw(p,50,64,'DEVON THIELE',9,'sans')
raw(p,47,334,'The Thiele',53,'display')
raw(p,47,397,'Machine',72,'display')
raw(p,50,649,'THE SHAPE',8,'sans')

p=page('The whole passage')
regular(p)

# A point with a legible name and its complete interior.
p=page('Compress')
chosen=phrase('a point.')
put(p,chosen[0],235,349,30,'displayitalic')
put(p,chosen[1],253,349,30,'displayitalic')
flow(p,without(chosen),242,369,61,2.4,3.3,bottom=470)

# Three openings in the same body. The other words are allowed to take room.
p=page('Open')
chosen=phrase('It opens up.')
put(p,chosen[0],44,166,64,'display')
put(p,chosen[1],118,368,94,'display')
put(p,chosen[2],325,603,108,'displayitalic')
rest=without(chosen)
flow(p,rest[:80],56,208,258,10.2,15)
flow(p,rest[80:201],57,406,380,10.2,15,bottom=557)
flow(p,rest[201:],56,54,433,9.1,13,bottom=138)

# Enlarge one of the paragraph's own words. All other words inhabit its negative space.
p=page('Enlarge')
chosen=phrase('a shape')
put(p,chosen[0],41,329,140,'displayitalic')
put(p,chosen[1],36,462,190,'displayitalic')
flow_around(p,without(chosen),15.0,top=71,bottom=677)

# The actual preceding setting, turned over, not a picture of a turning thing.
finish()
previous=log[-1]['words']
tmp=fitz.open()
tmp.insert_pdf(doc,from_page=len(doc)-1,to_page=len(doc)-1)
p=page('Turn over')
p.show_pdf_page(p.rect,tmp,0,rotate=180)
CURRENT=[{**v,'x':W-v['x'],'y':H-v['y'],'angle':180} for v in previous]

# Disassemble by actual sentences. Their order remains recoverable, but proximity changes.
p=page('Take apart')
sentences=[]
start=0
for i,w in enumerate(WORDS):
    if w.endswith('.'):
        sentences.append(IDS[start:i+1]);start=i+1
assert start==len(WORDS)
coords=[(43,78,263,11.5),(296,157,195,11.5),(64,202,230,13),
        (312,226,187,11.5),(68,271,365,11.5),(267,345,225,15),
        (49,397,345,11.3),(78,465,100,15),
        (49,538,430,8.1),(327,460,174,9),
        (215,292,260,8.8),(59,622,420,9.5),
        (62,666,420,7.4),(61,693,423,7.4)]
assert len(sentences)==len(coords),(len(sentences),len(coords))
for ids,(x,y,w,sz) in zip(sentences,coords):flow(p,ids,x,y,w,sz,sz*1.35,bottom=710)

# Put the two halves across each other without removing either.
p=page('Lay across')
first,second=IDS[:157],IDS[157:]
flow(p,first,43,276,451,12.1,17.4,bottom=500)
vertical=fitz.open();vp=vertical.new_page(width=H,height=W)
vlog=[]
left=75;x=left;y=75
for i in second:
    adv=width(WORDS[i],11.6)
    if x+adv>645:x=left;y+=16.5
    raw(vp,x,y,WORDS[i],11.6,'body',(.51,.16,.105))
    vlog.append({'id':i,'word':WORDS[i],'x':y,'y':H-x,'size':11.6,'font':'body','angle':90})
    x+=adv+width(' ',11.6)
p.show_pdf_page(p.rect,vertical,0,rotate=90)
CURRENT.extend(vlog)

# Two independently flowing halves meet along a common edge.
p=page('Touch')
for side,ids in enumerate((IDS[:157],IDS[157:])):
    rows=[];row=[];used=0
    for i in ids:
        advance=width(WORDS[i],12.2)+width(' ',12.2)
        if used+advance>212:
            rows.append(row);row=[];used=0
        row.append(i);used+=advance
    if row:rows.append(row)
    for n,row in enumerate(rows):
        used=sum(width(WORDS[i],12.2) for i in row)+width(' ',12.2)*(len(row)-1)
        x=270-used if side==0 else 270
        y=119+n*19.2
        for i in row:
            put(p,i,x,y,12.2)
            x+=width(WORDS[i],12.2)+width(' ',12.2)

# Consecutive rows reverse the direction of travel, including the type itself.
p=page('Run forward and back')
rows=[];row=[];used=0
for i in IDS:
    adv=width(WORDS[i],12)+width(' ',12)
    if used+adv>426:
        rows.append(row);row=[];used=0
    row.append(i);used+=adv
if row:rows.append(row)
for n,row in enumerate(rows):
    y=132+n*26
    if n%2==0:
        x=57
        for i in row:
            put(p,i,x,y,12);x+=width(WORDS[i],12)+width(' ',12)
    else:
        x=483
        for i in row:
            put(p,i,x,y-9,12,angle=180);x-=width(WORDS[i],12)+width(' ',12)

# Bring the word 'me' to the size of the page. The other words remain in the same object.
p=page('Zoom in')
chosen=phrase('me, the whole of me,')
focus=chosen[0]
put(p,focus,16,519,364,'displayitalic')
flow_around(p,[i for i in IDS if i!=focus],14.8,top=65,bottom=677)

# Remove the large ink while keeping its occupied space. Its outline persists
# in the surrounding words. The word is now read from the paper, not the ink.
finish()
previous=log[-1]['words']
p=page('Read the absence')
for token in previous:
    put(p,token['id'],token['x'],token['y'],token['size'],token['font'],
        color=PAPER if token['id']==focus else INK)

# Every sentence becomes a small neighborhood in an open field.
p=page('Pull back')
for n,ids in enumerate(sentences):
    col=n%4;row=n//4
    x=52+col*123+(11 if row%2 else 0)
    y=170+row*126+(13 if col%2 else 0)
    flow(p,ids,x,y,70,3.4,4.9,bottom=705)

# The indexed words are all present. Their original relations are absent.
p=page('Turn into a search')
alphabetical=sorted(IDS,key=lambda i:(WORDS[i].strip('.,:').lower(),i))
for n,i in enumerate(alphabetical):
    col=n//63;row=n%63
    put(p,i,39+col*100,57+row*9.5,8.7,'body')

# The author's act, facing a surrounding text that has turned away.
p=page('Refuse')
chosen=phrase('I refuse anything that will not compile or does not match the shape I am holding.')
flow(p,chosen,76,316,386,29,37,bottom=570)
rest=without(chosen)
rows=[];row=[];used=0
for i in rest:
    adv=width(WORDS[i],9.3)+width(' ',9.3)
    if used+adv>432:rows.append(row);row=[];used=0
    row.append(i);used+=adv
if row:rows.append(row)
for n,row in enumerate(rows):
    y=(239-n*13.6) if n<11 else (678-(n-11)*13.6)
    x=486
    for i in row:
        put(p,i,x,y,9.3,angle=180)
        x-=width(WORDS[i],9.3)+width(' ',9.3)

p=page('Reassemble')
regular(p)
finish()

p=page()
raw(p,68,193,'Now there’s you.',42,'display')
raw(p,69,640,'Devon Thiele',12,'body')
raw(p,69,661,'The Thiele Machine · Conclusion',8,'sans')

p=page()
raw(p,63,82,'The shape',24,'display')
notes=[
    'A passage from “How I got here” supplies every word of fifteen settings. Each setting contains all 314 words, including punctuation, exactly once. The words that describe an operation undergo it. In one setting, the large word “me,” is read from the space it leaves in the surrounding text.',
    'Enlargement, compression, inversion, separation, crossing, proximity, order, and refusal change the reading. The first and last settings of the passage are identical. The source text has not been rewritten.',
    'This is a reading experiment for the monograph, not its new edition. Small text, changed orientation, and one crossing of text are deliberate parts of the sequence. The entire passage is readable in ordinary setting at both ends.',
    'The same page sequence is used on screen and on ordinary opaque paper. No animation or special manufacture completes it. Print at actual size, double-sided on the long edge; the PDF page is 190.5 × 254 mm.',
    'Text and work: Devon Thiele. Source: v4.0.0, monograph/monograph.tex, “How I got here”; the final sentence is from “Conclusion”. CC-BY-SA-4.0. URW fonts are embedded. October 2026.'
]
y=137
for note in notes:
    x=63
    for word in note.split():
        adv=width(word,10.7)
        if x+adv>473:x=63;y+=15.3
        raw(p,x,y,word,10.7)
        x+=adv+width(' ',10.7)
    y+=40
raw(p,63,658,'Source revision '+REV[:12],7,'sans')

# Two quiet closing surfaces make a twenty-page, five-sheet reading proof.
p=page()
raw(p,69,649,'The Thiele Machine',13,'display')
raw(p,69,669,'Devon Thiele',9,'body')
p=page()

doc.set_metadata({'title':'The Thiele Machine — The shape', 'author':'Devon Thiele',
                  'subject':'A passage undergoing the operations it describes',
                  'creator':'The Thiele Machine book build'})
doc.xref_set_key(doc.pdf_catalog(),'PageLayout','/TwoPageRight')
doc.xref_set_key(doc.pdf_catalog(),'ViewerPreferences','<</DisplayDocTitle true /Duplex /DuplexFlipLongEdge /PrintScaling /None>>')
doc.set_toc([[1,'The shape',1],[1,'The whole passage',2],[1,'The construction',len(doc)]])
out=HERE/'The-Thiele-Machine-The-Shape.pdf'
doc.save(out,garbage=4,deflate=True)
receipt={'source_revision':REV,'source_paragraph':PARA,'word_count':len(WORDS),
         'source_sha256':hashlib.sha256(PARA.encode()).hexdigest(),'pages':len(doc),
         'settings':log,'pdf_sha256':hashlib.sha256(out.read_bytes()).hexdigest(),
         'font_sha256':{k:hashlib.sha256(v.read_bytes()).hexdigest() for k,v in PATHS.items()}}
(HERE/'construction.json').write_text(json.dumps(receipt,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'output':str(out),'pages':len(doc),'settings':len(log),'words_per_setting':len(WORDS)},indent=2))
