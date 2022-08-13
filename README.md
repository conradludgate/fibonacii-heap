# fibonacii_heap

[Fibonacii Heap](https://en.wikipedia.org/wiki/Fibonacci_heap) is a form of priority queue
that features constant time push with an average logarithmic pop.

In practice, they are slower than binary heaps, despite having better complexity

## Benchmarks

| Name | Test |
| --- | --- |
| insert/n | performs 2<sup>n</sup> inserts into the heap |
| pop/n | performs 2<sup>n</sup> pops from a heap of size 2<sup>n</sup> |
| pop1/n | performs a single pop from a heap of size 2<sup>n</sup> |

### Fibonacii Heap

```
fibonacii/insert/10     time:   [30.338 µs 30.585 µs 30.881 µs]
fibonacii/insert/11     time:   [63.569 µs 63.850 µs 64.167 µs]
fibonacii/insert/12     time:   [130.63 µs 131.12 µs 131.59 µs]
fibonacii/insert/13     time:   [266.99 µs 269.30 µs 271.98 µs]

fibonacii/pop/10        time:   [80.527 µs 81.042 µs 81.917 µs]
fibonacii/pop/11        time:   [202.34 µs 202.68 µs 203.14 µs]
fibonacii/pop/12        time:   [470.80 µs 471.32 µs 471.99 µs]
fibonacii/pop/13        time:   [1.0504 ms 1.0513 ms 1.0522 ms]

fibonacii/pop1/10       time:   [3.2672 µs 3.2844 µs 3.3007 µs]
fibonacii/pop1/11       time:   [6.8214 µs 6.9715 µs 7.1301 µs]
fibonacii/pop1/12       time:   [13.952 µs 14.476 µs 15.061 µs]
fibonacii/pop1/13       time:   [27.145 µs 27.806 µs 28.695 µs]
```

From this data, we can see that:

1. `insert` is constant time
2. `pop` is average logarithmic time
3. `pop1` executes in linear time (worst case example)

### Binary Heap

```
binary/insert/10        time:   [2.5520 µs 2.5645 µs 2.5780 µs]
binary/insert/11        time:   [4.7433 µs 4.7686 µs 4.7959 µs]
binary/insert/12        time:   [9.1789 µs 9.2832 µs 9.4064 µs]
binary/insert/13        time:   [18.284 µs 18.368 µs 18.458 µs]

binary/pop/10           time:   [11.706 µs 11.736 µs 11.768 µs]
binary/pop/11           time:   [30.506 µs 30.577 µs 30.659 µs]
binary/pop/12           time:   [71.859 µs 71.883 µs 71.909 µs]
binary/pop/13           time:   [169.44 µs 169.58 µs 169.68 µs]

binary/pop1/10          time:   [48.880 ns 51.656 ns 53.981 ns]
binary/pop1/11          time:   [80.705 ns 86.656 ns 91.623 ns]
binary/pop1/12          time:   [94.414 ns 104.18 ns 112.66 ns]
binary/pop1/13          time:   [117.77 ns 130.94 ns 143.25 ns]
```

From this data, we can see that:

1. `insert` is average constant time
2. `pop` is logarithmic time
3. `pop1` is logarithmic time
4. binary heaps are fast compared to fibonacii heaps
