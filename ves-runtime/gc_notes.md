# GC Notes
A set of notes compiled while reading the GC handbook.

## Memory Terminology

| Term                      | Definition                                                                                                                                                                                                                                    |
| -------                   | ----------                                                                                                                                                                                                                                    |
| Word                      | The size of the system's native pointer (64 bits on most systems, 32 bits or smaller in wasm and embedded systems).                                                                                                                           |
| Heap                      | A contiguous array of words or a set of discontiguous blocks of contiguous words.                                                                                                                                                             |
| Granule                   | The smallest unit of allocation, typically a word or a double word, depending on alignment requirements.                                                                                                                                      |
| Chunk                     | A large contiguous group of granules.                                                                                                                                                                                                         |
| Cell                      | A generally smaller contiguous group of granules. May be allocated or free, wasted, or unusable.                                                                                                                                              |
| Object                    | A cell allocated for use by the application. Usually assumed to be a contiguous array of addressable bytes or words, divided into slots or fields.                                                                                            |
| Object Field              | A reference or a scaler non-reference value with an associated name.                                                                                                                                                                          |
| Reference                 | A canonical pointer to the head of the object (the first address) or an offset from the head.                                                                                                                                                 |
| Canonical Pointer         | A pointer with the first 47 bits arbitrary, but the bits from 48 to 63 set to the 47th bit (this requirement forbids pointer tagging). See [this wikipedia page](https://en.wikipedia.org/wiki/X86-64#Canonical_form_addresses) for more info |
| Object Header             | A field with metadata used by the runtime system, commonly (but not always) stored at the head of an object.                                                                                                                                  |
| Derived Pointer           | A pointer obtained by adding an offset to an object's canonical pointer.                                                                                                                                                                      |
| Interior Pointer          | A derived pointer to an internal object field.                                                                                                                                                                                                |
| Block                     | An aligned chunk of a particular size, usually a power of two.                                                                                                                                                                                |
| Frame                     | A large 2^k sized portion of the address space, where a space is possible discontiguous collection of chunks or objects that receive similar treatment by the system.                                                                         |
| Page                      | Defined by the hardware and operating system's virtual memory mechanism (4kB by default on Linux and Windows)                                                                                                                                 |
| Card                      | A 2^k aligned chunk, smaller than  page, related to some schemes for remembering cross-space pointers (see Section 11.8 in the book)                                                                                                          |
| Heap (Object Graph)       | A directed graph whose nodes are heap objects and whose directed edges are references to heap objects stored in their fields.                                                                                                                 |

## GC Terminology

| Term              | Definition                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              |
| ----              | ----------                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              |
| Mutator           | The entity that executes the application code, which allocates new objects and mutates the object graph by changing reference fields so that they refer to different destination objects. The reference fields may be contained in heap objects as well as other places known as *roots*, such as static variables, stack, and so on. As a result of such reference updates, any object can end up disconnected from the root, that is, unreachable  by following any sequence of edges from the roots. |
| Collector         | The entity that executes the garbage collection code, which discovers unreachable objects and reclaims their storage.                                                                                                                                                                                                                                                                                                                                                                                   |
| Allocator         | The entity that that supports two operations: *allocate*, which reserves the underlying memory storage for an object, and *free*, which returns that storage to the allocator for subsequent re-use.                                                                                                                                                                                                                                                                                                    |
| Roots             | A finite set of objects directly accessible by the mutator without going through other objects. In practice, the root usually comprise static/global storage and thread local storage such as the stack.                                                                                                                                                                                                                                                                                                |
| *P                | Operation: Dereferencing a pointer.                                                                                                                                                                                                                                                                                                                                                                                                                                                                     |
| &E                | Operation: Obtaining the address of the object E. For example, `&N[i]` describes the ith field of N.                                                                                                                                                                                                                                                                                                                                                                                                    |
| Pointers(N)       | The addresses of all fields of N.                                                                                                                                                                                                                                                                                                                                                                                                                                                                       |
| Pointers          | The set of all pointer field of all objects in the heap.                                                                                                                                                                                                                                                                                                                                                                                                                                                |
| Nodes             | The set of all allocated objects in the heap.                                                                                                                                                                                                                                                                                                                                                                                                                                                           |
| Liveness          | An object is considered live if it will be accessed at some time in the future execution of the mutator. A correct garbage collector never reclaims live objects.                                                                                                                                                                                                                                                                                                                                       |
| Reachability      | Given two objects, M and N, the object N is reachable from M if it can be reached by following a chain of pointers, starting from some field *f* of M. In other words, N is reachable from M if there exists at least one path from M to N.                                                                                                                                                                                                                                                             |

Note: there may be multiple mutators and multiple collectors

### Additional Mutator Terminology
| Term               | Definition                                                                                                                              |
| -----              | ---------                                                                                                                               |
| `New()`            | The operation that obtains a new heap object from the heap allocator.                                                                   |
| `Read(obj, f)`       | The operation that accesses an object field in memory or returns the value stored at that location.                                     |
| `Write(obj, f, val)` | Th operation that modifies a particular location in memory                                                                              |
| Barrier            | An action that results in synchronous or asynchronous communication with the collector. There are *read barriers* and *write barriers*. |


## Garbage Collection Approaches

| Approach                 | Definition        | Pros    | Cons      |
| ------------------------ | -----------       | ------- | --------- |
| Mark-Sweep Collection    | (TODO): Chapter 2 | (TODO)  | (TODO)    |
| Copying Collection       | (TODO): Chapter 3 | (TODO)  | (TODO)    |
| Mark-Compact Collection  | (TODO): Chapter 4 | (TODO)  | (TODO)    |
| Reference Counting       | (TODO): Chapter 5 | (TODO)  | (TODO)    |

### Mark-Sweep Collection Algorithm
The naive mark-and-sweep algorithm from  the beginning of chapter 2.
```rs
fn new(roots, heap) {
    ref = allocate()

    if ref is none {
        collect(roots, heap)
        ref = allocate()
        if ref is none {
            panic("Out of memory")
        }
    }

    return ref
}

fn collect(roots, heap) {
    mark_roots(roots)  // a.k.a trace
    sweep(heap)
}

fn mark_roots(roots) {
    worklist = initialize()

    for field in roots {
        ref = *field
        if ref is some && not ref.is_marked() {
            ref.set_marked()
            worklist.add(ref)
            // NOTE: inside the loop to minimize worrklist size.
            // A different implementation may desire moving the call out of the loop
            mark(worklist)
        }
    }
}

fn initialize() {
    return [] /* empty */
}

fn mark(worklist) {
    while not worklist.is_empty() {
        ref = worklist.remove()
        for field in Pointers(ref) {
            child = *field
            if child is some and not child.is_marked() {
                child.set_marked()
                worklist.add(child)
            }
        }
    }
}

fn sweep(heap) {
    cursor = heap.cursor()

    while not cursor.is_at_end() {
        obj = cursor.object()

        if obj.is_marked() {
            obj.set_unmarked()
        } else {
            free(obj)
        }

        cursor.move_next()
    }
}
```
