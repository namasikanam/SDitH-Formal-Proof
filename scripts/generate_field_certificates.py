#!/usr/bin/env python3
"""Untrusted certificate discovery for the exact Table-2 binary moduli.

The generated Lean files contain data and kernel-checked `decide` proofs.
Python output is never admitted as a theorem or as an irreducibility assumption.
Run from the repository root. No external packages are needed.
"""

from pathlib import Path


def multiply(a, b):
    result = 0
    while a:
        if a & 1:
            result ^= b
        a >>= 1
        b <<= 1
    return result


def divide(a, b):
    quotient = 0
    while a and a.bit_length() >= b.bit_length():
        shift = a.bit_length() - b.bit_length()
        quotient ^= 1 << shift
        a ^= b << shift
    return quotient, a


def euclid(a, b):
    steps = []
    while b != 1:
        assert b != 0
        q, r = divide(a, b)
        steps.append((q, r))
        a, b = b, r
    return steps


def bits(n):
    return "[" + ", ".join("true" if n >> i & 1 else "false"
                           for i in range(n.bit_length())) + "]"


def generate(name, degree, lower, checks):
    f = (1 << degree) | sum(1 << k for k in lower)
    residues = [2]
    quotients = []
    for _ in range(degree):
        quotient, residue = divide(multiply(residues[-1], residues[-1]), f)
        quotients.append(quotient)
        residues.append(residue)
    assert residues[-1] == 2
    lines = [
        "import SDitH.Proofs.BinaryPolynomialCertificate",
        "",
        "/-! Generated certificate data for one exact Table-2 polynomial.",
        "Regenerate with scripts/generate_field_certificates.py. Every arithmetic",
        "certificate is checked by ordinary `decide`; the interpreter and the",
        "algebraic meaning of the checks are proved in the imported modules. -/",
        "",
        f"namespace SDitH.Proofs.FieldCertificates.{name}",
        "",
        "open Polynomial BinaryPolynomialCertificate",
        "set_option maxRecDepth 4096",
        "set_option maxHeartbeats 0",
        "",
        f"def modulusBits : Bits := {bits(f)}",
        "",
    ]
    expression = " + ".join("1" if k == 0 else "X" if k == 1 else f"X ^ {k}"
                            for k in [degree, *lower])
    lines += ["theorem polynomial_modulusBits :",
              f"    polynomial modulusBits = ({expression} : (ZMod 2)[X]) := by",
              "  simp only [modulusBits, polynomial, Bool.false_eq_true, if_false, if_true,",
              "    mul_zero, add_zero, zero_add, mul_one]",
              "  ring", ""]
    for i, residue in enumerate(residues):
        lines += [f"def r{i} : Bits := {bits(residue)}", ""]
    for i, quotient in enumerate(quotients):
        lines += [f"def q{i} : Bits := {bits(quotient)}", ""]
    starts = list(range(0, degree, 16))
    for start in starts:
        stop = min(start + 16, degree)
        lines += [f"def chunk{start} : List SquareStep := ["]
        for i in range(start, stop):
            comma = "," if i + 1 < stop else ""
            lines += [f"  ⟨q{i}, r{i + 1}⟩{comma}"]
        initial = "[false, true]" if start == 0 else f"r{start}"
        lines += ["]", "", f"theorem checked{start} :",
                  f"    checkChain modulusBits {initial} chunk{start} = true := by",
                  "  decide", "",
                  f"theorem length{start} : chunk{start}.length = {stop-start} := rfl", "",
                  f"theorem finish{start} (start : Bits) :",
                  f"    finish start chunk{start} = r{stop} := rfl", ""]
    chunks = " ++ ".join(f"chunk{start}" for start in starts)
    lines += [f"def steps : List SquareStep := {chunks}", "",
              "theorem checked : checkChain modulusBits [false, true] steps = true := by",
              "  simp only [steps, checkChain_append, finish_append,"]
    lines += ["    " + ", ".join(f"finish{start}" for start in starts[:-1]) + ",",
              "    " + ", ".join(f"checked{start}" for start in starts) + ", Bool.true_and]", ""]
    for m in [*checks, degree]:
        prefix = " ++ ".join(f"chunk{start}" for start in starts if start < m)
        prefixstarts = [start for start in starts if start < m]
        lines += [f"def prefix{m} : List SquareStep := {prefix}", ""]
        lines += [f"theorem residue{m} : polynomial modulusBits ∣",
                  f"    X ^ (2 ^ {m}) - polynomial r{m} := by",
                  f"  have hc : checkChain modulusBits [false, true] prefix{m} = true := by",
                  f"    simp only [prefix{m}, checkChain_append, finish_append,",
                  "      " + ", ".join(f"finish{start}" for start in prefixstarts[:-1]) + ",",
                  "      " + ", ".join(f"checked{start}" for start in prefixstarts) + ", Bool.true_and]",
                  f"  have hl : prefix{m}.length = {m} := by",
                  f"    simp only [prefix{m}, List.length_append, " +
                  ", ".join(f"length{start}" for start in prefixstarts) + "]",
                  f"  have hf : finish [false, true] prefix{m} = r{m} := by",
                  f"    simp only [prefix{m}, finish_append, " +
                  ", ".join(f"finish{start}" for start in prefixstarts) + "]",
                  f"  simpa only [hl, hf] using chain_dvd modulusBits prefix{m} hc", ""]
    for m in checks:
        transcript = euclid(f, residues[m] ^ 2)
        estarts = list(range(0, len(transcript), 8))
        lines += [f"def er{m}_0 : Bits := {bits(residues[m] ^ 2)}", ""]
        for i, (q, r) in enumerate(transcript):
            lines += [f"def er{m}_{i+1} : Bits := {bits(r)}", ""]
        for start in estarts:
            stop = min(start + 8, len(transcript))
            first = "modulusBits" if start == 0 else f"er{m}_{start-1}"
            second = f"er{m}_{start}"
            lines += [f"def echunk{m}_{start} : List SquareStep := ["]
            for i in range(start, stop):
                q, r = transcript[i]
                comma = "," if i + 1 < stop else ""
                lines += [f"  ⟨{bits(q)}, er{m}_{i+1}⟩{comma}"]
            lines += ["]", "", f"theorem echecked{m}_{start} :",
                      f"    checkRemainders {first} {second} echunk{m}_{start} = true := by decide", "",
                      f"theorem efinish{m}_{start} :",
                      f"    euclidFinish {first} {second} echunk{m}_{start} =",
                      f"      (er{m}_{stop-1}, er{m}_{stop}) := rfl", ""]
        echunks = "[]"
        for start in reversed(estarts):
            echunks = f"echunk{m}_{start} ++ ({echunks})"
        lines += [f"def euclid{m} : List SquareStep := {echunks}", "",
                  f"theorem euclidChecked{m} :",
                  f"    checkEuclid modulusBits (add r{m} [false, true]) euclid{m}",
                  "      = true := by",
                  f"  have hi : add r{m} [false, true] = er{m}_0 := by decide",
                  "  rw [hi]",
                  f"  simp only [euclid{m}, checkEuclid_append, " +
                  ", ".join(f"echecked{m}_{start}, efinish{m}_{start}" for start in estarts) +
                  ", Bool.true_and]",
                  "  rfl", "", f"theorem coprime{m} :",
                  f"    IsCoprime (polynomial modulusBits) (X ^ (2 ^ {m}) - X) := by",
                  f"  exact coprime_frobenius_of_euclid modulusBits r{m}",
                  f"    {m} euclid{m} residue{m} euclidChecked{m}", ""]
    lines += [f"theorem full : polynomial modulusBits ∣ X ^ (2 ^ {degree}) - X := by",
              f"  simpa only [r{degree}, polynomial, Bool.false_eq_true,",
              "    if_false, if_true, mul_zero, add_zero, mul_one, zero_add] using",
              f"    residue{degree}", "", f"end SDitH.Proofs.FieldCertificates.{name}", ""]
    target = Path("SDitH/Proofs/FieldCertificates") / f"{name}.lean"
    target.parent.mkdir(exist_ok=True)
    target.write_text("\n".join(lines))


if __name__ == "__main__":
    generate("CategoryI", 128, [7, 2, 1, 0], [64])
    generate("CategoryIII", 192, [7, 2, 1, 0], [64, 96])
    generate("CategoryV", 256, [10, 5, 2, 0], [128])
