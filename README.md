# Forge Tool Documentation
## Protocol Implementations
The protocol implementation is stored in the prot_impl directory currently contatining the following protocol implementations

- Needham Schroeder (in two_nonce.rkt and two_nonce.frg respectively)

(Remaining files in prot_impl not mentioned in the above list used for debugging)

The files in this repo are not enough to run these examples you have to download both forge and the crypto tool used for implementing this from this [repo](https://github.com/tnelson/Forge/tree/main) the tool itself is located at this [link](https://github.com/tnelson/Forge/tree/main/forge/domains/crypto) inside the repo.
## Documentation
This repository also contains documentation/explanation for the code written for the protocols in prot_impl, and for the base.frg file in the forge tool. base.frg contains the model used for verification of protocols itself.
The documentation itself is located in the documentation folder. The index for the documentation is located at ./forge_tool_doc/main.md
