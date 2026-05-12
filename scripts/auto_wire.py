import json
import re
import os

def load_orphans():
    orphans = []
    with open("sorries.jsonl") as f:
        for line in f:
            data = json.loads(line)
            if data.get("b", "") == "" and data.get("c") == "open":
                orphans.append(data["s"])
    return orphans

def wire_tex():
    orphans = load_orphans()
    tex_files = [os.path.join("tex/sections", f) for f in os.listdir("tex/sections") if f.endswith(".tex")]
    
    # Common mappings
    mappings = {
        "closedForm_pathIntegral_primitive_exists": "lem:path-integral-primitive",
        "euler_char_eq_formula": "lem:tbh-r12",
        "identityChartCoeff_contDiff": "lem:section-localRepr-identity-chart-contdiff",
        "identityChartCoeff_tendsto_zero": "lem:section-localRepr-identity-chart-contdiff",
        "moduleFinite_realHarmonic": "lem:hle-r14",
        "finiteDim_realHarmonic": "lem:hle-r14",
        "isHolomorphic_of_contMDiff": "lem:impl-meromorphic-lift"
    }

    # Heuristic matching
    def heuristic(orphan, label):
        o = orphan.lower().replace("_", "")
        l = label.lower().replace("lem:", "").replace("thm:", "").replace("-", "")
        if o in l or l in o:
            return True
        return False

    for file_path in tex_files:
        with open(file_path) as f:
            content = f.read()
        
        # 1. Match by mappings
        for orphan, label in mappings.items():
            pattern = rf"(\\label\{{{label}\}}.*?\\lean\{{)([^}}]*?)(\}})"
            if label in content:
                content = re.sub(pattern, lambda m: f"{m.group(1)}{m.group(2)}{',' if m.group(2) else ''}{orphan}{m.group(3)}", content, flags=re.DOTALL)
        
        # 2. Heuristic matching for the rest
        for orphan in orphans:
            if orphan in mappings: continue
            # Look for labels
            labels = re.findall(r"\\label\{([^}]+)\}", content)
            for label in labels:
                if heuristic(orphan, label):
                    pattern = rf"(\\label\{{{label}\}}.*?\\lean\{{)([^}}]*?)(\}})"
                    content = re.sub(pattern, lambda m: f"{m.group(1)}{m.group(2)}{',' if m.group(2) else ''}{orphan}{m.group(3)}", content, flags=re.DOTALL)
                    break
        
        # 3. Clean up double commas
        content = content.replace(",,", ",")
        
        with open(file_path, "w") as f:
            f.write(content)

if __name__ == "__main__":
    wire_tex()
