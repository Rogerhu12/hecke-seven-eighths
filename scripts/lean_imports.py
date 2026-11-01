"""Read Lean's import header without treating documentation examples as imports."""
import re

def strip_comments(text):
    out=[];i=0;depth=0;line=False;string=False
    while i<len(text):
        pair=text[i:i+2];c=text[i]
        if line:
            if c=='\n':line=False;out.append(c)
            else:out.append(' ')
            i+=1;continue
        if depth:
            if pair=='/-':depth+=1;out.extend('  ');i+=2
            elif pair=='-/':depth-=1;out.extend('  ');i+=2
            else:out.append('\n' if c=='\n' else ' ');i+=1
            continue
        if string:
            out.append(c)
            if c=='\\' and i+1<len(text):out.append(text[i+1]);i+=2;continue
            if c=='"':string=False
            i+=1;continue
        if pair=='--':line=True;out.extend('  ');i+=2;continue
        if pair=='/-':depth=1;out.extend('  ');i+=2;continue
        if c=='"':string=True
        out.append(c);i+=1
    return ''.join(out)

def imports(text):
    result=[];depth=0
    # Stop after the import header: large generated proof bodies need not be
    # scanned, and documentation snippets later in the file cannot add edges.
    for raw in text.splitlines():
        i=0;visible=[]
        while i<len(raw):
            pair=raw[i:i+2]
            if depth:
                if pair=='/-':depth+=1;i+=2
                elif pair=='-/':depth-=1;i+=2
                else:i+=1
                continue
            if pair=='/-':depth=1;i+=2;continue
            if pair=='--':break
            visible.append(raw[i]);i+=1
        line=''.join(visible).strip()
        if not line or line in {'module','prelude'}:continue
        match=re.fullmatch(r'(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?([\w.]+(?:\s+[\w.]+)*)',line)
        if not match:break
        result.extend(match.group(1).split())
    return result
