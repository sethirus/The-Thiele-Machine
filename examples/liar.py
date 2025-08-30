import os

def check_my_own_code():
    # Read this file's source code
    with open(__file__, 'r', encoding='utf-8') as f:
        source_code = f.read()


    # Paradox: check for and against the word 'paradox'
    assert 'paradox' in source_code, "Paradox check 1 failed."
    assert 'paradox' not in source_code, "Paradox check 2 failed."

    print("Success! This program is logically consistent.")

if __name__ == "__main__":
    check_my_own_code()
