import sys
import re
import os

files_to_fix = [
    "Jacobian/Periods/PullbackNaturality.lean",
    "Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean",
    "Jacobian/TraceDegree/PushforwardBasis.lean",
    "Jacobian/Solution.lean",
    "Jacobian/ComplexTorus/Defs.lean",
    "Jacobian/HolomorphicForms/SectionSupNorm.lean",
    "Jacobian/Periods/CurveIntegralSubpath.lean",
    "Jacobian/ComplexTorus/Basic.lean",
    "Jacobian/HolomorphicForms/SectionMetric.lean",
    "Jacobian/ComplexTorus/ChartBall.lean",
    "Jacobian/ComplexTorus/LocalSectionRightInv.lean",
    "Jacobian/ComplexTorus/TransitionSubMem.lean",
    "Jacobian/Periods/PathIntegralChartCorrectSplit.lean",
    "Jacobian/Periods/PathIntegralViaCoverWithRefine.lean",
    "Jacobian/Periods/PathIntegralViaCoverWithRefinementInvariant.lean",
    "Jacobian/Periods/PathIntegralViaCoverWithTrans.lean",
    "Jacobian/TraceDegree/PullbackBasis.lean"
]

def fix_file(file_path):
    if not os.path.exists(file_path):
        print(f"File not found: {file_path}")
        return

    with open(file_path, 'r') as f:
        lines = f.readlines()

    new_lines = []
    import_finished = False
    option_added = False
    
    i = 0
    while i < len(lines):
        line = lines[i]
        
        # Add option after imports
        if not option_added:
            if line.strip().startswith('import '):
                import_finished = True
            elif import_finished and line.strip() == '' and not any(l.strip().startswith('import ') for l in lines[i:]):
                # We found a gap after the last import
                pass
            elif import_finished and not line.strip().startswith('import ') and line.strip() != '':
                # First non-import, non-empty line after imports
                new_lines.append("\nset_option linter.unusedSectionVars false\n")
                option_added = True
        
        # Skip omit blocks
        if line.strip().startswith('omit '):
            # Check if it's a single line omit or multi-line
            if ' in' in line:
                # Single line or starts a block that ends with ' in' on some line
                while i < len(lines) and ' in' not in lines[i]:
                    i += 1
                i += 1
                continue
            else:
                # Just 'omit ...' without 'in'
                # These usually continue until a non-indented line or just one line?
                # Actually, in Lean 4, 'omit' is a command.
                # If it doesn't have 'in', it usually applies until the end of the section or 'include'.
                # Let's just remove the 'omit' line itself if it doesn't have 'in'.
                i += 1
                continue
        
        new_lines.append(line)
        i += 1
    
    # If option still not added (e.g. no imports?), add it at the top
    if not option_added:
         # Find first line that is not a comment or empty
         added = False
         for idx, line in enumerate(new_lines):
             if line.strip() and not line.strip().startswith('--') and not line.strip().startswith('/-'):
                 new_lines.insert(idx, "\nset_option linter.unusedSectionVars false\n")
                 added = True
                 break
         if not added:
             new_lines.append("\nset_option linter.unusedSectionVars false\n")

    with open(file_path, 'w') as f:
        f.writelines(new_lines)
    print(f"Fixed {file_path}")

if __name__ == "__main__":
    for f in files_to_fix:
        fix_file(f)
