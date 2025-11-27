
path = "coq/thielemachine/verification/BridgeDefinitions.v"
with open(path, "r") as f:
    lines = f.readlines()

# Find check_transition_compose
indices = [i for i, line in enumerate(lines) if "Lemma check_transition_compose" in line]
print(f"Found {len(indices)} occurrences.")

if len(indices) > 1:
    # Delete the first one
    start = indices[0]
    # Find end of proof (Qed)
    end = start
    for i in range(start, len(lines)):
        if "Qed." in lines[i]:
            end = i + 1
            break

    print(f"Deleting first occurrence lines {start}-{end}")
    del lines[start:end]

    with open(path, "w") as f:
        f.writelines(lines)
elif len(indices) == 1:
    # Check if run_n_add is defined before it
    lemma_idx = indices[0]
    run_n_idx = -1
    for i, line in enumerate(lines):
        if "Lemma run_n_add" in line:
            run_n_idx = i
            break

    if run_n_idx == -1:
        print("Error: run_n_add not found!")
    elif run_n_idx > lemma_idx:
        print("Error: run_n_add defined AFTER check_transition_compose. Swapping/Fixing.")
        # Extract the lemma and move it to end
        start = lemma_idx
        end = start
        for i in range(start, len(lines)):
            if "Qed." in lines[i]:
                end = i + 1
                break
        lemma_lines = lines[start:end]
        del lines[start:end]
        lines.extend(lemma_lines)
        with open(path, "w") as f:
            f.writelines(lines)
    else:
        print("Order is correct.")
