import socket
import ssl
from cryptography import x509
from cryptography.hazmat.backends import default_backend
from cryptography.hazmat.primitives.asymmetric.rsa import RSAPublicKey

# The target is a household name.
HOSTNAME = 'www.paypal.com'

context = ssl.create_default_context()
with socket.create_connection((HOSTNAME, 443)) as sock:
    with context.wrap_socket(sock, server_hostname=HOSTNAME) as ssock:
        cert_der = ssock.getpeercert(binary_form=True)
        if cert_der is None:
            print("Failed to get certificate")
            exit(1)
        cert = x509.load_der_x509_certificate(cert_der, default_backend())
        public_key = cert.public_key()

        if not isinstance(public_key, RSAPublicKey):
            print(f"Public key is not RSA: {type(public_key).__name__}")
            exit(1)

        # This is the number. The target. N.
        n = public_key.public_numbers().n

        print("="*80)
        print(f"Successfully acquired live public key from: {HOSTNAME}")
        print(f"Key Type: {type(public_key).__name__}")
        print(f"Bit Length: {n.bit_length()}")
        print("="*80)
        print(f"N = {n}")