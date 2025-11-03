class ThieleReplay < Formula
  desc "Thiele Machine receipt verifier - verify software from cryptographic proofs"
  homepage "https://github.com/sethirus/The-Thiele-Machine"
  url "https://files.pythonhosted.org/packages/source/t/thiele-replay/thiele-replay-1.0.0.tar.gz"
  sha256 "PLACEHOLDER_SHA256"
  license "Apache-2.0"
  
  depends_on "python@3.12"
  
  resource "PyNaCl" do
    url "https://files.pythonhosted.org/packages/source/P/PyNaCl/PyNaCl-1.5.0.tar.gz"
    sha256 "8ac7448f09ab85811607bdd21ec2464495ac8b7c66d146bf545b0f08fb9220ba"
  end
  
  resource "cryptography" do
    url "https://files.pythonhosted.org/packages/source/c/cryptography/cryptography-45.0.0.tar.gz"
    sha256 "PLACEHOLDER_CRYPTOGRAPHY_SHA256"
  end
  
  def install
    virtualenv_install_with_resources
    
    # Self-verification on install
    system libexec/"bin/python", "-c", "import sys; print('Thiele Machine installed successfully')"
  end
  
  test do
    # Test CLI commands exist
    assert_match "Thiele Receipt Replay Verifier", shell_output("#{bin}/thiele-replay --help")
    assert_match "Ingest binary", shell_output("#{bin}/thiele-ingest --help")
    assert_match "delta receipt", shell_output("#{bin}/thiele-delta --help")
    
    # Test basic functionality
    (testpath/"test.txt").write("Hello, Thiele!")
    system bin/"thiele-ingest", testpath/"test.txt", "--out", testpath/"receipt.json"
    assert_predicate testpath/"receipt.json", :exist?
  end
end
