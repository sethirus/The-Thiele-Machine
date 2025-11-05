{ lib
, python3Packages
, fetchFromGitHub
}:

python3Packages.buildPythonApplication rec {
  pname = "thiele-receipts";
  version = "1.0.0";
  format = "pyproject";

  src = fetchFromGitHub {
    owner = "sethirus";
    repo = "The-Thiele-Machine";
    rev = "v${version}";
    sha256 = "REPLACE_WITH_ACTUAL_SHA256";
  };

  propagatedBuildInputs = with python3Packages; [
    pynacl
    cryptography
    jsonschema
    requests
  ];

  nativeBuildInputs = with python3Packages; [
    setuptools
  ];

  # Only include receipt-related files
  postPatch = ''
    # Keep only necessary files
    find . -maxdepth 1 -type f ! -name 'pyproject.toml' ! -name 'create_receipt.py' -delete || true
    find . -maxdepth 1 -type d ! -name '.' ! -name 'verifier' ! -name 'docs' ! -name 'tests' -exec rm -rf {} + || true
  '';

  # Install wrapper scripts
  postInstall = ''
    # Create thiele-receipt command
    cat > $out/bin/thiele-receipt <<EOF
    #!${python3Packages.python.interpreter}
    import sys
    from pathlib import Path
    sys.path.insert(0, str(Path('$out/lib/python${python3Packages.python.pythonVersion}/site-packages')))
    from create_receipt import main
    if __name__ == '__main__':
        main()
    EOF
    chmod +x $out/bin/thiele-receipt

    # Create thiele-verify command
    cat > $out/bin/thiele-verify <<EOF
    #!${python3Packages.python.interpreter}
    import sys
    from pathlib import Path
    sys.path.insert(0, str(Path('$out/lib/python${python3Packages.python.pythonVersion}/site-packages')))
    from verifier.replay import main_cli
    if __name__ == '__main__':
        main_cli()
    EOF
    chmod +x $out/bin/thiele-verify
  '';

  # Disable tests for now (they require the full project)
  doCheck = false;

  meta = with lib; {
    description = "Cryptographically verifiable software receipts";
    homepage = "https://github.com/sethirus/The-Thiele-Machine";
    license = licenses.asl20;
    maintainers = [ ];
    mainProgram = "thiele-receipt";
  };
}
