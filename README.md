# A Simple DSA for Rust

This library implements basic functions for using DSA keys in rust,
including key generation, signing and verification via PKCS 1.5, and
encryption and decryption via OAEP.

Here's the thing, though.

If you're using this library, I hope you're implementing compatibility with some
old protocol. There's a lot of those, which is why I wrote the library.  The key
is: it's an old protocol, not a new one. Because if you're using this library as
part of a new protocol, you're making a mistake. Use
[RSA](http://github.com/acw/simple_rsa) for those. Or, better yet, your favorite
elliptic curve variant.
