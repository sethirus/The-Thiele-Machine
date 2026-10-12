#!/usr/bin/env python3
"""Typeset current words into space not occupied by an earlier assertion.
Copyright 2026 Devon Thiele. CC-BY-SA-4.0.
"""
from pathlib import Path
import json
import math
import fitz
import numpy as np
from PIL import Image

HERE = Path(__file__).resolve().parent
FONTS = Path('/usr/share/fonts/opentype/urw-base35')
W,H = 540,720
DISPLAY = FONTS/'NimbusRoman-Regular.otf'
BODY = FONTS/'P052-Roman.otf'
SANS = FONTS/'NimbusSans-Regular.otf'
ITALIC = FONTS/'P052-Italic.otf'
bodyfont = fitz.Font(fontfile=str(BODY))
displayfont = fitz.Font(fontfile=str(DISPLAY))
INK=(.06,.045,.04)
OLD=(.48,.14,.105)
records = json.loads((HERE/'construction.json').read_text())['cases']

def write(p, x,y,s,size=12,font=BODY,color=INK):
    name=font.stem.replace('-','')
    p.insert_font(fontname=name,fontfile=str(font))
    p.insert_text((x,y),s,fontname=name,fontsize=size,color=color)

def plate(lines, size, positions=None):
    d=fitz.open()
    p=d.new_page(width=W,height=H)
    for i,line in enumerate(lines):
        x,y = positions[i] if positions else (30,190+i*size*1.05)
        write(p,x,y,line,size,DISPLAY,OLD)
    return d

def occupancy(plate_doc, pad=3):
    pix=plate_doc[0].get_pixmap(matrix=fitz.Matrix(1,1), colorspace=fitz.csGRAY, alpha=False)
    a=np.frombuffer(pix.samples,np.uint8).reshape(H,W)<245
    padded=a.copy()
    for dy in range(-pad,pad+1):
        for dx in range(-pad,pad+1):
            # Zero padding: the page edge is not periodic.
            y0,y1=max(0,dy),min(H,H+dy)
            x0,x1=max(0,dx),min(W,W+dx)
            padded[y0:y1,x0:x1]|=a[y0-dy:y1-dy,x0-dx:x1-dx]
    return padded

def available(mask,y,size):
    high=max(0,math.floor(y-size*.83))
    low=min(H,math.ceil(y+size*.3))
    line=mask[high:low,:].any(axis=0)
    spans=[]
    start=None
    for x in range(35,506):
        free=not line[x]
        if free and start is None:start=x
        if (not free or x==505) and start is not None:
            end=x if not free else x+1
            if end-start>34:spans.append((start,end))
            start=None
    return spans

def flow(p, words, mask, size=12.0, top=80,bottom=625):
    n=0
    positions=[]
    for y in np.arange(top,bottom,size*1.55):
        for left,right in available(mask,y,size):
            x=left
            while n<len(words):
                word=words[n]
                width=bodyfont.text_length(word,fontsize=size)
                if x+width>right:break
                write(p,x,float(y),word,size)
                positions.append({'word':word,'x':x,'y':float(y),'width':width,'size':size})
                x+=width+bodyfont.text_length(' ',fontsize=size)
                n+=1
        if n==len(words):break
    return words[n:],positions

doc=fitz.open()
specs=[
    (records[1], ['It','isn’t','faster.'],164,[(36,216),(36,384),(29,552)]),
    (records[2], ['a fixed','program','couldn’t.'],126,[(28,200),(25,352),(28,508)]),
    (records[3], ['Rival','events','leave no','such trail.'],116,[(28,164),(27,290),(28,416),(24,542)])]
audits=[]
for rec,words,size,positions in specs:
    pl=plate(words,size,positions)
    mask=occupancy(pl,pad=3)
    p=doc.new_page(width=W,height=H)
    p.show_pdf_page(p.rect,pl,0)
    remaining,places=flow(p,rec['after'].split(),mask)
    write(p,35,42,'EARLIER WORDS / CURRENT WORDS',7,SANS,OLD)
    write(p,35,671,rec['change'][:12]+' → '+rec['current_revision'][:12],7,SANS,OLD)
    write(p,35,652,'Earlier wording in large type. Current passage occupies the remaining space.',7.2,ITALIC)
    while remaining:
        p=doc.new_page(width=W,height=H)
        remaining,newplaces=flow(p,remaining,np.zeros((H,W),dtype=bool))
        places+=newplaces
    audits.append({'case':rec['title'],'words':len(places),'expected':len(rec['after'].split())})
doc.set_metadata({'title':'The Thiele Machine — spatial typesetting trial','author':'Devon Thiele'})
doc.save(HERE/'spatial-trial.pdf',garbage=4,deflate=True)
print(audits)
