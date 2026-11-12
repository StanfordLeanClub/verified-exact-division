"""Extract and relocate the one leaf COFF function into a self-contained image.

This extractor is untrusted. Lean must check the resulting bytes against the
independently specified instruction program before the object is accepted.
"""
from pathlib import Path
import struct,hashlib,json,argparse

def extract(path):
    data=Path(path).read_bytes()
    machine,nsec,_,symoff,nsym,optlen,_=struct.unpack_from('<HHIIIHH',data)
    if machine!=0x8664 or optlen:raise ValueError('Expected x86-64 COFF object')
    sections=[]
    for i in range(nsec):
        off=20+40*i
        name=data[off:off+8].split(b'\0')[0].decode()
        size,ptr,reloc=struct.unpack_from('<III',data,off+16)
        nr=struct.unpack_from('<H',data,off+32)[0]
        sections.append(dict(name=name,body=data[ptr:ptr+size],reloc=reloc,nreloc=nr))
    strings=symoff+18*nsym
    symbols={};i=0
    while i<nsym:
        off=symoff+18*i
        if data[off:off+4]==b'\0'*4:
            start=strings+struct.unpack_from('<I',data,off+4)[0]
            name=data[start:data.index(b'\0',start)].decode()
        else:name=data[off:off+8].split(b'\0')[0].decode()
        val,sec,typ,storage,aux=struct.unpack_from('<IhHBB',data,off+8)
        symbols[i]=dict(name=name,value=val,section=sec,type=typ,storage=storage)
        i+=1+aux
    entry=[s for s in symbols.values() if s['name']=='certified_div3']
    if len(entry)!=1 or entry[0]['value']!=0:raise ValueError('Unexpected function entry')
    text=sections[entry[0]['section']-1]
    if text['name']!='.text':raise ValueError('Entry is not executable text')
    image=bytearray(text['body']);text_size=len(image)
    image.extend(b'\0'*((-len(image))%32))
    offsets={};relocations=[]
    for k in range(text['nreloc']):
        pos,idx,kind=struct.unpack_from('<IIH',data,text['reloc']+10*k)
        if kind!=4:raise ValueError('Only RIP-relative 32-bit constant relocations allowed')
        s=symbols[idx]
        if s['section']<=0:raise ValueError('External symbol/call not allowed')
        sec=sections[s['section']-1]
        if sec['name']!='.rdata' or len(sec['body'])!=4 or s['value']!=0:
            raise ValueError('Only four-byte readonly constants allowed')
        word=sec['body']
        if word not in offsets:
            offsets[word]=len(image);image.extend(word)
        addend=struct.unpack_from('<i',image,pos)[0]
        target=offsets[word]+addend
        struct.pack_into('<i',image,pos,target-(pos+4))
        relocations.append(dict(offset=pos,target=target,word=word.hex()))
    return bytes(image),dict(text_bytes=text_size,image_bytes=len(image),relocations=relocations,
        object_sha256=hashlib.sha256(data).hexdigest(),image_sha256=hashlib.sha256(image).hexdigest())

def emit(obj,destination):
    image,meta=extract(obj)
    destination=Path(destination);destination.mkdir(parents=True,exist_ok=True)
    (destination/'image.bin').write_bytes(image)
    (destination/'image.json').write_text(json.dumps(meta,indent=2)+'\n')
    asm=['.text','.p2align 5','.globl certified_div3','.globl certified_div3_image_end','certified_div3:']
    asm+=['.byte '+','.join(f'0x{x:02x}' for x in image[i:i+16]) for i in range(0,len(image),16)]
    asm+=['certified_div3_image_end:']
    (destination/'image.S').write_text('\n'.join(asm)+'\n')
    print(json.dumps(meta,indent=2))

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('object');ap.add_argument('destination')
    a=ap.parse_args();emit(a.object,a.destination)
