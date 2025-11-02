class ThieleReplay < Formula
  desc "Thiele Machine receipt verifier - verify software from cryptographic proofs"
  homepage "https://github.com/sethirus/The-Thiele-Machine"
  url "https://github.com/sethirus/The-Thiele-Machine/archive/v1.0.0.tar.gz"
  sha256 "PLACEHOLDER_SHA256"
  license "Apache-2.0"
  
  depends_on "python@3.12"
  
  def install
    # Install Python verifier
    libexec.install Dir["verifier/*"]
    
    # Create wrapper script
    (bin/"thiele-replay").write <<~EOS
      #!/bin/bash
      exec "#{Formula["python@3.12"].opt_bin}/python3" "#{libexec}/replay.py" "$@"
    EOS
    
    chmod 0755, bin/"thiele-replay"
    
    # Self-verification on install
    system bin/"thiele-replay", "bootstrap_receipts"
  end
  
  test do
    # Verify bootstrap receipts
    system bin/"thiele-replay", "bootstrap_receipts"
    
    # Check global digest
    output = shell_output("#{bin}/thiele-replay bootstrap_receipts/050_kernel_emit.json --print-digest")
    expected = File.read("tests/expected_kernel_sha256.txt").strip
    assert_equal expected, output.strip
  end
end
