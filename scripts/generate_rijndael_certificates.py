#!/usr/bin/env python3
"""Propose byte inverse witnesses; Lean checks all entries in its kernel.

These Python calculations have no proof authority. The S-box specification is
read from the Lean transcription of FIPS 197 Table 4, not replaced by this script.
"""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent.parent


def multiply(a, b):
    result = 0
    for i in range(8):
        if a >> i & 1:
            result ^= b
        b = ((b << 1) & 255) ^ (0x1b if b >> 7 else 0)
    return result


def vector(name, values):
    assert len(values) == 256
    rows = [', '.join(f'0x{v:02x}' for v in values[i:i+16]) for i in range(0, 256, 16)]
    return f'def {name} : Vector Byte 256 := #v[\n  ' + ',\n  '.join(rows) + '\n]\n'


def main():
    inverse = [0] + [next(j for j in range(1, 256) if multiply(i, j) == 1)
                       for i in range(1, 256)]
    source = (ROOT / 'SDitH/Spec/RijndaelByte.lean').read_text()
    raw = source.split('def sboxTable : Vector Byte 256 := #v[', 1)[1].split(']', 1)[0]
    sbox = [int(x, 16) for x in re.findall(r'0x[0-9a-f]{2}', raw)]
    assert sorted(sbox) == list(range(256))
    inverse_sbox = [sbox.index(i) for i in range(256)]
    text = '''import SDitH.Spec.RijndaelByte
import Mathlib.Tactic

/-! Generated proposed witnesses, checked for every byte by the Lean kernel.
Regenerate with scripts/generate_rijndael_certificates.py. No external
calculation or table is accepted as an assumption. -/

namespace SDitH.Proofs.RijndaelByteCertificates

open Spec.RijndaelByte
set_option maxRecDepth 4096
set_option maxHeartbeats 8000000
set_option Elab.async false

'''
    text += vector('inverseTable', inverse) + '\n'
    text += vector('inverseSboxTable', inverse_sbox) + '\n'
    text += '''def inverse (b : Byte) : Byte := inverseTable[b.toFin]
def inverseSbox (b : Byte) : Byte := inverseSboxTable[b.toFin]

theorem inverse_zero : inverse 0 = 0 := by decide

theorem inverse_checked : ∀ b : Byte, b ≠ 0 → mul b (inverse b) = 1 := by
  decide +kernel

theorem sbox_checked : ∀ b : Byte, sbox b = affine (inverse b) := by
  decide +kernel

theorem inverse_sbox_checked : ∀ b : Byte, inverseSbox (sbox b) = b := by
  decide +kernel

theorem sbox_inverse_checked : ∀ b : Byte, sbox (inverseSbox b) = b := by
  decide +kernel

end SDitH.Proofs.RijndaelByteCertificates
'''
    (ROOT / 'SDitH/Proofs/RijndaelByteCertificates.lean').write_text(text)


if __name__ == '__main__':
    main()
