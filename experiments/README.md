# Experiments
This crate contains micro-benchmarks and small experiments that try out different vm implementation strategies.
All benchmarks currently listed were run on a 6-core i7-8700K (max clock 4.7GHz).

## Current Findings
1. `enum` opcodes vs byte opcodes. See the `fibonacci` benchmark.
    It appears that enum opcodes are similar to or slightly faster than byte opcodes, while byte opcodes are more memory-efficient. Although, larger benchmarks are required to determine this confidently.

    | Benchmark (GC: Rc, unchecked)          | Lo        | Md        | Hi        |
    |----------------------------------------|-----------|-----------|-----------|
    | Byte opcodes: fib-iterative(200)       | 77.876 us | 78.332 us | 78.855 us |
    | Enum Opcodes: fib-iterative(200)       | 75.002 us | 75.833 us | 76.941 us |
    | Enum Opcodes w/ IC: fib-iterative(200) | 52.626 us | 53.014 us | 53.555 us |
    | rust baseline: fib-iterative(200)      | 0.2151 us | 0.2164 us | 0.2178 us |

    | Benchmark (GC: Naive Mark-Sweep)            | Lo        | Md        | Hi        |
    |---------------------------------------------|-----------|-----------|-----------|
    | Byte opcodes: fib-iterative(200)            | 26.914 us | 27.024 us | 27.153 us |
    | Enum Opcodes: fib-iterative(200)            | 23.906 us | 24.121 us | 24.427 us |
    | Enum Opcodes w/ IC: fib-iterative(200)      | 11.327 us | 11.387 us | 11.462 us |
    | Enum Opcodes w/ Inst IC: fib-iterative(200) | 9.8167 us | 9.8869 us | 9.9837 us |
    | rust baseline: fib-iterative(200)           | 212.06 ns | 213.48 ns | 214.91 ns |

    ### TODOs
    1. Check if this holds for bigger opcode sizes (e.g. 4 bytes).
    2. Is there a way to hack variable-length opcodes into the enum representation?

2. Field lookups: linear search vs hash functions (benched: sip13, fnv, ahash). See the `hashes` benchmark.
    Linear search with direct manual string comparisons (i.e. `==`) is faster than all hashmaps if the number of elements < 10. With 10+ items, ahash beats
    all other solutions, including linear search, especially as the the number of elements grows.

    | Benchmark (5 elements, 10K accesses, key size = 1..=10) | Lo        | Md        | Hi        |
    |---------------------------------------------------------|-----------|-----------|-----------|
    | Linear Search                                           | 45.478 ns | 46.107 ns | 46.836 ns |
    | SipHash13                                               | 65.042 ns | 65.943 ns | 67.077 ns |
    | Fnv HashMap                                             | 52.157 ns | 52.978 ns | 53.888 ns |
    | AHash HashMap                                           | 50.711 ns | 51.435 ns | 52.268 ns |

    | Benchmark (10 elements, 10K accesses, key size = 1..=10) | Lo        | Md        | Hi        |
    |----------------------------------------------------------|-----------|-----------|-----------|
    | Linear Search                                            | 85.092 ns | 86.365 ns | 87.905 ns |
    | SipHash13                                                | 89.659 ns | 92.101 ns | 94.982 ns |
    | Fnv HashMap                                              | 77.822 ns | 78.931 ns | 80.231 ns |
    | AHash HashMap                                            | 71.638 ns | 72.935 ns | 74.500 ns |

    | Benchmark (20 elements, 10K accesses, key size = 1..=10) | Lo        | Md        | Hi        |
    |----------------------------------------------------------|-----------|-----------|-----------|
    | Linear Search                                            | 186.90 ns | 189.22 ns | 192.44 ns |
    | SipHash13                                                | 137.30 ns | 138.60 ns | 140.09 ns |
    | Fnv HashMap                                              | 112.09 ns | 114.30 ns | 117.06 ns |
    | AHash HashMap                                            | 107.24 ns | 110.02 ns | 113.79 ns |

    | Benchmark (30 elements, 10K accesses, key size = 1..=10) | Lo        | Md        | Hi        |
    |----------------------------------------------------------|-----------|-----------|-----------|
    | Linear Search                                            | 255.72 ns | 257.29 ns | 259.08 ns |
    | SipHash13                                                | 167.20 ns | 168.90 ns | 170.87 ns |
    | Fnv HashMap                                              | 133.24 ns | 134.67 ns | 136.36 ns |
    | AHash HashMap                                            | 131.50 ns | 132.78 ns | 134.26 ns |

    | Benchmark (100 elements, 10K accesses, key size = 1..=10) | Lo        | Md        | Hi        |
    |-----------------------------------------------------------|-----------|-----------|-----------|
    | Linear Search                                             | 568.65 ns | 572.62 ns | 577.84 ns |
    | SipHash13                                                 | 201.15 ns | 202.32 ns | 203.79 ns |
    | Fnv HashMap                                               | 157.18 ns | 158.20 ns | 159.37 ns |
    | AHash HashMap                                             | 151.21 ns | 152.73 ns | 154.62 ns |

    ### TODOs
    1. Try modifying the linear search to use pre-computed string hashes for comparisons (+ hash probing).
    2. Is an adaptive solution that would try to use a linear array for small objects but a hashmap for large objects worth the runtime overhead and implementation complexity?
