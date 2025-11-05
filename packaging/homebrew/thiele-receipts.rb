class ThieleReceipts < Formula
  desc "Cryptographically verifiable software receipts"
  homepage "https://github.com/sethirus/The-Thiele-Machine"
  url "https://github.com/sethirus/The-Thiele-Machine/archive/refs/tags/v1.0.0.tar.gz"
  sha256 "REPLACE_WITH_ACTUAL_SHA256"
  license "Apache-2.0"

  depends_on "python@3.12"

  resource "PyNaCl" do
    url "https://files.pythonhosted.org/packages/a7/22/27582568be639dfe22ddb3902225f91f2f17ceff88ce80e4db396c8986da/PyNaCl-1.5.0.tar.gz"
    sha256 "8ac7448f09ab85811607bdd21ec2464495ac8b7c66d146bf545b0f08fb9220ba"
  end

  resource "cryptography" do
    url "https://files.pythonhosted.org/packages/source/c/cryptography/cryptography-45.0.0.tar.gz"
    sha256 "REPLACE_WITH_ACTUAL_SHA256"
  end

  def install
    virtualenv_install_with_resources

    # Create wrapper scripts
    (bin/"thiele-receipt").write <<~EOS
      #!/bin/bash
      exec "#{libexec}/bin/python3" "#{libexec}/create_receipt.py" "$@"
    EOS

    (bin/"thiele-verify").write <<~EOS
      #!/bin/bash
      exec "#{libexec}/bin/python3" "#{libexec}/verifier/replay.py" "$@"
    EOS

    chmod 0755, bin/"thiele-receipt"
    chmod 0755, bin/"thiele-verify"
  end

  test do
    # Test receipt creation
    (testpath/"test.txt").write "Hello, World!"
    system bin/"thiele-receipt", "test.txt", "--output", "receipt.json"
    assert_predicate testpath/"receipt.json", :exist?

    # Verify the receipt
    system bin/"thiele-verify", "receipt.json", "--dry-run"
  end
end
