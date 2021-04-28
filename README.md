## Ves

This repository hosts the implementation of the Ves language. The goals are to be:

* Embeddable
* Fast
* Ergonomic
* Lightweight

The goals are in no particular order. To elaborate, the language is meant to serve as the scripting layer in larger applications, such as games or web servers. In terms of speed, it should be competitive with other languages in the same category (dynamic, interpreted). Since it is a high-level language, writing code in it should be a low-friction experience. Finally, it should have a relatively small memory footprint.

### Status

The language is past the design phase, and we're currently implementing the MVP. The language itself will be interpreted by a stack-based bytecode virtual machine. So far, we've implemented a parser, resolver, and constant folder.