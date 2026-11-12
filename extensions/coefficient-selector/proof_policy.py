"""Fail-closed checks for the published Lean replay, including negative controls."""
from collections import Counter
import re

ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

def audit_output(output, expected):
    entries=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",output)
    if Counter(n for n,_ in entries)!=Counter(expected):
        raise ValueError('Missing, duplicated, or unexpected axiom-audit declarations')
    for name,body in entries:
        axioms={a.strip() for a in body.split(',') if a.strip()}
        if axioms-ALLOWED:
            raise ValueError(f'{name}: forbidden dependencies {sorted(axioms-ALLOWED)}')
    if re.search(r"declaration uses ['`]sorry|\berror:",output):
        raise ValueError('Lean reported an admitted declaration or error')
    return len(entries)

def source_policy(source):
    # Additional strict token policy, not a Lean parser or a security boundary
    # against malicious authors. Dependencies of audited statements are checked
    # from Lean's output separately.
    if re.search(r'\b(sorry|admit|native_decide|axiom)\b',source):
        raise ValueError('Forbidden proof token in replay source')

def parser_negative_controls():
    good="'probe' depends on axioms: [propext, Classical.choice, Quot.sound]"
    audit_output(good,['probe'])
    bad=[('', ['probe']), (good+'\n'+good,['probe']),
         (good.replace('Quot.sound','sorryAx'),['probe']),
         (good.replace('Quot.sound','inventedAssumption'),['probe']),
         (good.replace('Quot.sound','Lean.ofReduceBool'),['probe'])]
    for output,expected in bad:
        try: audit_output(output,expected)
        except ValueError: pass
        else: raise RuntimeError('Audit negative control was incorrectly accepted')
    for token in ['sorry','admit','native_decide','axiom']:
        try: source_policy('theorem probe : True := by '+token)
        except ValueError: pass
        else: raise RuntimeError('Source negative control was incorrectly accepted')
    return len(bad)+4
