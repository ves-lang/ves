## Ves

This repository hosts the implementation of the Ves language. The goals are to be:

* Embeddable
* Fast
* Ergonomic
* Lightweight

The goals are in no particular order. To elaborate, the language is meant to serve as the scripting layer in larger applications, such as games or web servers. In terms of speed, it should be competitive with other languages in the same category (dynamic, interpreted). Since it is a high-level language, writing code in it should be a low-friction experience. Finally, it should have a relatively small memory footprint.

Check out the [tour](./TOUR.md) for a quick overview of the language. For more examples, take a look at the [VM tests](./ves-backend/tests).

### Status

The language is past the design phase, and we're currently implementing the MVP. The parsing and bytecode emit stages of compilation are fully implemented, and the VM is at about 75%.