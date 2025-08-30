import os

def check_my_own_code():
    # Read this file's source code
    with open(__file__, 'r', encoding='utf-8') as f:
        source_code = f.read()

    # Statements about the presence of a string in the source
    statement1 = "This source code contains the string 'paradox'."
    statement2 = "This source code does not contain the string 'paradox'."

    assert statement1 in source_code, "Paradox check 1 failed."
    assert statement2 in source_code, "Paradox check 2 failed."

    print("Success! This program is logically consistent.")

if __name__ == "__main__":
    check_my_own_code()
