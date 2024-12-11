# coq-evm

This might or might not become a full Ethereum Virtual Machine in Coq someday.

Right now you can have the hash functions:

	- Keccak-256
	- SHA256
	- RIPEMD160
	- BLAKE2b (F function only)
	
All those functions use native Coq integers for speed. All of them are tested against their Go implementations.

## Checking

	./configure    # just does coq_makefile
	make

## Testing

This needs Go.
	
	cd test
	./configure    # gives a warning but it's OK
	make