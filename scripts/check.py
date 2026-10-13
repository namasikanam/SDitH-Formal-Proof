#!/usr/bin/env python3
"""Build and audit proof trust. This never labels the formalization complete."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parent.parent
EXPECTED_PDF = "22dfed06d179afa759139487dca9c8f8d4a7cfea22bcedcb7736b50ce5b01c83"


def without_comments(text: str) -> str:
    """Remove nested Lean block comments and line comments for a conservative scan."""
    out = []
    i, depth = 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        else:
            out.append(text[i])
            i += 1
    if depth:
        raise SystemExit("Unclosed Lean comment in source scan")
    return "".join(out)


def main() -> None:
    digest = hashlib.sha256((ROOT / "sdith-v3.0.pdf").read_bytes()).hexdigest()
    if digest != EXPECTED_PDF:
        raise SystemExit("Source PDF differs from the reviewed version")
    reference_pdfs = {
        "source/standards/NIST.FIPS.202.pdf":
            "1592607831ff0908cc590632ce371c6c95e94025bb1a0c8ae90a4d0ec1ed025e",
    }
    reference_pdfs['source/standards/SHAKE128_Msg0.pdf'] = '3013d904e0f6cebc8dad6393cbf3eed4d1a537b3b3dc5e7b48552ff597942974'
    reference_pdfs['source/standards/SHAKE128_Msg5.pdf'] = '5c69e3650f3a5c97448dc1a6b48c9c0f743c22152310464daa94f78d3ae6fe09'
    reference_pdfs['source/standards/SHAKE128_Msg1605.pdf'] = '6889b092e4f25164b50c893841c79fe2289bdddf2654405ee2b23f682eed05ad'
    reference_pdfs['source/standards/SHAKE256_Msg0.pdf'] = 'd736c1a93eb6440e1e6b640402e31ea5258281b2b9237f84ea0ba4186518fc59'
    reference_pdfs['source/standards/SHAKE256_Msg5.pdf'] = '6256c84773b28315a638a89f6295023da2cb9ef3c8b632b38754a0e5e119db4e'
    reference_pdfs['source/standards/SHAKE256_Msg1605.pdf'] = '6df1800147a841536cb91d3a1a3712769fff9bc1905d0a86aef5fc77347a3338'
    reference_pdfs['source/standards/NIST.FIPS.197-upd1.pdf'] = '62c86eb567f13edb8f71826e985da870b04ef6381634f303cdb16e84d47becd1'
    reference_pdfs['source/standards/Rijndael-V2-1999.pdf'] = '763d33ef26d06b4e76a0986e276444332df8143c96f72a9ee6e0205becec9c3d'
    reference_pdfs['source/standards/Rijndael-2002.pdf'] = '1f83fcd8cc93776adb6735253ef122483d2aea56d74912ce9271f3b2aa4e7578'
    for name, expected in reference_pdfs.items():
        if hashlib.sha256((ROOT / name).read_bytes()).hexdigest() != expected:
            raise SystemExit(f"Reference PDF differs from the reviewed version: {name}")
    forbidden = re.compile(
        r"\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|"
        r"trustCompiler|run_tac|elab|macro|syntax)\b"
    )
    sources = [ROOT / "SDitH.lean", *sorted((ROOT / "SDitH").rglob("*.lean"))]
    for path in sources:
        match = forbidden.search(without_comments(path.read_text()))
        if match:
            raise SystemExit(f"Forbidden proof/source mechanism {match[0]} in {path}")
    # Keep large kernel-evaluated SHAKE certificates from competing for memory
    # on a fresh build. All modules are still included in the full build below.
    for strength in (128, 256):
        for bits in (0, 5, 1605):
            subprocess.run(
                ["lake", "build", f"SDitH.Proofs.SHAKEExample{strength}Msg{bits}"],
                cwd=ROOT, check=True,
            )
    for target in (
        "SDitH.Proofs.RijndaelByteCertificates",
        "SDitH.Proofs.AESExample",
        "SDitH.Proofs.Rijndael256Examples",
    ):
        subprocess.run(["lake", "build", target], cwd=ROOT, check=True)
    subprocess.run(["lake", "build"], cwd=ROOT, check=True)
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    for package in manifest["packages"]:
        dependency = ROOT / manifest["packagesDir"] / package["name"]
        revision = subprocess.check_output(
            ["git", "-C", str(dependency), "rev-parse", "HEAD"], text=True
        ).strip()
        if revision != package["rev"]:
            raise SystemExit(f"Dependency revision mismatch: {package['name']}")
        subprocess.run(
            ["git", "-C", str(dependency), "diff", "--quiet", "HEAD", "--"], check=True
        )
    subprocess.run(["lake", "env", "lean", "audit/Axioms.lean"], cwd=ROOT, check=True)
    print("Build and axiom audit passed. Coverage remains separately tracked; not completion.")


if __name__ == "__main__":
    main()
