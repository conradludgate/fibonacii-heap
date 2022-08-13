#![warn(clippy::pedantic)]
//! A priority queue implemented with a fibonacii heap.
//!
//! Insertion is *O*(1) and popping the smallest element has *O*(log(*n*)) amortised time complexity.
//! Checking the smallest element is *O*(1).
//!
//! # Examples
//!
//! This is a larger example that implements [Dijkstra's algorithm][dijkstra]
//! to solve the [shortest path problem][sssp] on a [directed graph][dir_graph].
//! It shows how to use [`Heap`] with custom types.
//!
//! [dijkstra]: https://en.wikipedia.org/wiki/Dijkstra%27s_algorithm
//! [sssp]: https://en.wikipedia.org/wiki/Shortest_path_problem
//! [dir_graph]: https://en.wikipedia.org/wiki/Directed_graph
//!
//! ```
//! use std::cmp::Ordering;
//! use fibonacii_heap::Heap;
//!
//! #[derive(Copy, Clone, Eq, PartialEq, PartialOrd, Ord)]
//! struct State {
//!     cost: usize,
//!     position: usize,
//! }
//!
//! // Each node is represented as a `usize`, for a shorter implementation.
//! struct Edge {
//!     node: usize,
//!     cost: usize,
//! }
//!
//! // Dijkstra's shortest path algorithm.
//!
//! // Start at `start` and use `dist` to track the current shortest distance
//! // to each node. This implementation isn't memory-efficient as it may leave duplicate
//! // nodes in the queue. It also uses `usize::MAX` as a sentinel value,
//! // for a simpler implementation.
//! fn shortest_path(adj_list: &Vec<Vec<Edge>>, start: usize, goal: usize) -> Option<usize> {
//!     // dist[node] = current shortest distance from `start` to `node`
//!     let mut dist: Vec<_> = (0..adj_list.len()).map(|_| usize::MAX).collect();
//!
//!     let mut heap = Heap::new();
//!
//!     // We're at `start`, with a zero cost
//!     dist[start] = 0;
//!     heap.push(State { cost: 0, position: start });
//!
//!     // Examine the frontier with lower cost nodes first (min-heap)
//!     while let Some(State { cost, position }) = heap.pop() {
//!         // Alternatively we could have continued to find all shortest paths
//!         if position == goal { return Some(cost); }
//!
//!         // Important as we may have already found a better way
//!         if cost > dist[position] { continue; }
//!
//!         // For each node we can reach, see if we can find a way with
//!         // a lower cost going through this node
//!         for edge in &adj_list[position] {
//!             let next = State { cost: cost + edge.cost, position: edge.node };
//!
//!             // If so, add it to the frontier and continue
//!             if next.cost < dist[next.position] {
//!                 heap.push(next);
//!                 // Relaxation, we have now found a better way
//!                 dist[next.position] = next.cost;
//!             }
//!         }
//!     }
//!
//!     // Goal not reachable
//!     None
//! }
//!
//! fn main() {
//!     // This is the directed graph we're going to use.
//!     // The node numbers correspond to the different states,
//!     // and the edge weights symbolize the cost of moving
//!     // from one node to another.
//!     // Note that the edges are one-way.
//!     //
//!     //                  7
//!     //          +-----------------+
//!     //          |                 |
//!     //          v   1        2    |  2
//!     //          0 -----> 1 -----> 3 ---> 4
//!     //          |        ^        ^      ^
//!     //          |        | 1      |      |
//!     //          |        |        | 3    | 1
//!     //          +------> 2 -------+      |
//!     //           10      |               |
//!     //                   +---------------+
//!     //
//!     // The graph is represented as an adjacency list where each index,
//!     // corresponding to a node value, has a list of outgoing edges.
//!     // Chosen for its efficiency.
//!     let graph = vec![
//!         // Node 0
//!         vec![Edge { node: 2, cost: 10 },
//!              Edge { node: 1, cost: 1 }],
//!         // Node 1
//!         vec![Edge { node: 3, cost: 2 }],
//!         // Node 2
//!         vec![Edge { node: 1, cost: 1 },
//!              Edge { node: 3, cost: 3 },
//!              Edge { node: 4, cost: 1 }],
//!         // Node 3
//!         vec![Edge { node: 0, cost: 7 },
//!              Edge { node: 4, cost: 2 }],
//!         // Node 4
//!         vec![]];
//!
//!     assert_eq!(shortest_path(&graph, 0, 1), Some(1));
//!     assert_eq!(shortest_path(&graph, 0, 3), Some(3));
//!     assert_eq!(shortest_path(&graph, 3, 0), Some(7));
//!     assert_eq!(shortest_path(&graph, 0, 4), Some(5));
//!     assert_eq!(shortest_path(&graph, 4, 0), None);
//! }
//! ```

mod ll;

/// A priority queue implemented with a fibonacii heap.
///
/// This will be a min-heap.
///
/// It is a logic error for an item to be modified in such a way that the
/// item's ordering relative to any other item, as determined by the [`Ord`]
/// trait, changes while it is in the heap. This is normally only possible
/// through [`Cell`], [`RefCell`], global state, I/O, or unsafe code. The
/// behavior resulting from such a logic error is not specified, but will
/// be encapsulated to the `Heap` that observed the logic error and not
/// result in undefined behavior. This could include panics, incorrect results,
/// aborts, memory leaks, and non-termination.
///
/// # Examples
///
/// ```
/// use fibonacii_heap::Heap;
///
/// let mut heap = Heap::new();
///
/// // We can use peek to look at the next item in the heap. In this case,
/// // there's no items in there yet so we get None.
/// assert_eq!(heap.peek(), None);
///
/// // Let's add some scores...
/// heap.push(1);
/// heap.push(5);
/// heap.push(2);
///
/// // Now peek shows the most important item in the heap.
/// assert_eq!(heap.peek(), Some(&1));
///
/// // If we instead pop these scores, they should come back in order.
/// assert_eq!(heap.pop(), Some(1));
/// assert_eq!(heap.pop(), Some(2));
/// assert_eq!(heap.pop(), Some(5));
/// assert_eq!(heap.pop(), None);
/// ```
///
/// ## Max-heap
///
/// Either [`core::cmp::Reverse`] or a custom [`Ord`] implementation can be used to
/// make `Heap` a max-heap. This makes `heap.pop()` return the largest
/// value instead of the greatest one.
///
/// ```
/// use fibonacii_heap::Heap;
/// use std::cmp::Reverse;
///
/// let mut heap = Heap::new();
///
/// // Wrap values in `Reverse`
/// heap.push(Reverse(1));
/// heap.push(Reverse(5));
/// heap.push(Reverse(2));
///
/// // If we pop these scores now, they should come back in the reverse order.
/// assert_eq!(heap.pop(), Some(Reverse(5)));
/// assert_eq!(heap.pop(), Some(Reverse(2)));
/// assert_eq!(heap.pop(), Some(Reverse(1)));
/// assert_eq!(heap.pop(), None);
/// ```
///
/// # Time complexity
///
/// | [push]  | [pop]          | [peek] |
/// |---------|----------------|--------|
/// | *O*(1)  | *O*(log(*n*))~ | *O*(1) |
///
/// The value for `pop` is an expected cost; the method documentation gives a
/// more detailed analysis.
///
/// [`core::cmp::Reverse`]: core::cmp::Reverse
/// [`Ord`]: core::cmp::Ord
/// [`Cell`]: core::cell::Cell
/// [`RefCell`]: core::cell::RefCell
/// [push]: Heap::push
/// [pop]: Heap::pop
/// [peek]: Heap::peek
/// [peek\_mut]: Heap::peek_mut
pub struct Heap<T> {
    children: ll::LinkedListTree<T>,
    scratch: Scratch<Box<ll::Node<T>>>,
    len: usize,
}
impl<T> Default for Heap<T> {
    fn default() -> Self {
        Self::new()
    }
}

struct Scratch<T> {
    space: Vec<Option<T>>,
}

impl<T> Scratch<T> {
    const fn new() -> Self {
        Self { space: Vec::new() }
    }

    fn reserve(&mut self, n: usize) {
        // A heap with `n` elements should have max-degree log2(n)+1.
        // This quantity can break if we get unlucky and remove only the small
        // degree nodes and leave large degree nodes unchecked.
        // This isn't a problem here though since we never decrease the space
        let new_len = (usize::BITS - n.leading_zeros()) as usize;
        let new_len = new_len.max(self.space.len());
        self.space.resize_with(new_len, || None);
    }

    /// # Safety
    /// Must have called reserve before hand
    unsafe fn space(&mut self, d: usize) -> &mut Option<T> {
        // Safety: space is guaranteed to be available (see reserve)
        self.space.get_unchecked_mut(d)
    }
}

impl<T> Heap<T> {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            children: ll::LinkedListTree::new(),
            scratch: Scratch::new(),
            len: 0,
        }
    }
}

impl<T: Ord> Heap<T> {
    /// Returns the length of the binary heap.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use fibonacii_heap::Heap;
    /// let mut heap = Heap::new();
    ///
    /// heap.push(3);
    /// heap.push(5);
    /// heap.push(1);
    ///
    /// assert_eq!(heap.len(), 3);
    /// ```
    #[must_use]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Checks if the fibonacii heap is empty.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use fibonacii_heap::Heap;
    /// let mut heap = Heap::new();
    ///
    /// assert!(heap.is_empty());
    ///
    /// heap.push(3);
    /// heap.push(5);
    /// heap.push(1);
    ///
    /// assert!(!heap.is_empty());
    /// ```
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Returns the smallest item in the fibonacii heap, or `None` if it is empty.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use fibonacii_heap::Heap;
    /// let mut heap = Heap::new();
    /// assert_eq!(heap.peek(), None);
    ///
    /// heap.push(2);
    /// heap.push(1);
    /// heap.push(5);
    /// assert_eq!(heap.peek(), Some(&1));
    /// ```
    ///
    /// # Time complexity
    ///
    /// Cost is *O*(1) in the worst case.
    #[must_use]
    pub fn peek(&self) -> Option<&T> {
        self.children.first()
    }

    /// Pushes an item onto the binary heap.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use fibonacii_heap::Heap;
    /// let mut heap = Heap::new();
    /// heap.push(3);
    /// heap.push(5);
    /// heap.push(1);
    ///
    /// assert_eq!(heap.len(), 3);
    /// assert_eq!(heap.peek(), Some(&1));
    /// ```
    ///
    /// # Time complexity
    ///
    /// Cost is *O*(1) in the worst case.
    pub fn push(&mut self, t: T) {
        let node = Box::new(ll::Node::new(t));
        self.scratch.reserve(self.len + 1);
        self.children.insert_node(node);
        self.len += 1;
    }

    /// Moves all the elements of `other` into `self`, leaving `other` empty.
    ///
    /// # Time complexity
    ///
    /// Cost is *O*(1) in the worst case.
    pub fn merge(&mut self, other: &mut Self) {
        match (&mut self.children.0, other.children.0.take()) {
            (Some(x), Some(mut y)) => {
                // swap so self is the minimum heap
                if x.first() > y.first() {
                    std::mem::swap(x, &mut y);
                }
                x.append(y);
                self.scratch.reserve(self.len + other.len);
                self.len += std::mem::replace(&mut other.len, 0);
            }
            (None, Some(y)) => {
                other.children.0 = Some(y);
                std::mem::swap(self, other);
            }
            (Some(_) | None, None) => {}
        }
    }

    /// Removes the smallest item from the binary heap and returns it, or `None` if it
    /// is empty.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use fibonacii_heap::Heap;
    /// let mut heap = Heap::new();
    /// heap.push(3);
    /// heap.push(5);
    /// heap.push(1);
    ///
    /// assert_eq!(heap.pop(), Some(1));
    /// assert_eq!(heap.pop(), Some(3));
    /// assert_eq!(heap.pop(), Some(5));
    /// assert_eq!(heap.pop(), None);
    /// ```
    ///
    /// # Time complexity
    ///
    /// Cost is *O*(log(*n*)) on average and  *O*(*n* + log(*n*)) in the worst case.
    ///
    /// The worst case is caused only after an insert of `n` elements, so the expected
    /// cost can be spread out to the [`push`](Heap::push) for an amortised cost of *O*(log(*n*))
    pub fn pop(&mut self) -> Option<T> {
        self.pop_inner().map(|x| x.into_inner())
    }

    fn pop_inner(&mut self) -> Option<Box<ll::Node<T>>> {
        let value = self.phase1()?;
        self.phase2();
        self.phase3();
        debug_assert_eq!(self.scratch.space.iter().flatten().count(), 0);
        Some(value)
    }

    /// phase2 - remove the minimum node
    fn phase1(&mut self) -> Option<Box<ll::Node<T>>> {
        self.children.pop_front_node().map(|mut value| {
            self.len -= 1;
            self.children.append_from_node(&mut value);
            debug_assert_eq!(value.degree(), 0);
            value
        })
    }

    /// phase2 - merge top level nodes with the same degree (to keep the heap logarithmic in size)
    fn phase2(&mut self) {
        debug_assert!(
            self.scratch.space.iter().flatten().next().is_none(),
            "scratch space should be empty before phase2"
        );

        while let Some(mut current) = self.children.pop_front_node() {
            loop {
                // Safety: reserve called by `push`
                let d = unsafe { self.scratch.space(current.degree()) };
                if let Some(v) = d.take() {
                    current = current.merge(v);
                } else {
                    d.replace(current);
                    break;
                }
            }
        }
    }

    /// phase3 - rebuild the heap (finding the new minimum node in the process)
    fn phase3(&mut self) {
        debug_assert!(
            self.children.is_empty(),
            "children should be empty before phase3"
        );

        for node in self.scratch.space.iter_mut().filter_map(Option::take) {
            self.children.insert_node(node);
        }
    }
}

impl<T: Ord> Extend<T> for Heap<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for i in iter {
            self.push(i);
        }
    }
}
impl<T: Ord> FromIterator<T> for Heap<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut heap = Heap::new();
        heap.extend(iter);
        heap
    }
}

#[cfg(test)]
mod tests {
    use std::fmt::Debug;

    use rand::{seq::SliceRandom, thread_rng};

    use super::Heap;

    #[track_caller]
    fn check<T: Ord + Debug>(heap: &mut Heap<T>, elems: impl IntoIterator<Item = T>) {
        let elems = elems.into_iter();
        let n = elems.size_hint().1.unwrap();
        for (i, elem) in elems.enumerate() {
            assert_eq!(heap.len(), n - i);
            assert_eq!(heap.peek(), Some(&elem));
            assert_eq!(heap.pop(), Some(elem));
        }

        assert!(heap.is_empty());
        assert_eq!(heap.peek(), None);
        assert_eq!(heap.pop(), None);
    }

    #[test]
    fn works() {
        const N: usize = 100;

        let mut heap = Heap::default();
        let mut elems: Vec<_> = (0..N).collect();
        elems.shuffle(&mut thread_rng());
        for i in elems {
            heap.push(i);
        }

        check(&mut heap, 0..N);
    }

    #[test]
    fn duplicates() {
        const N: usize = 10;
        let mut heap = Heap::default();
        let mut elems = vec![];

        for i in 0..N {
            for j in 0..N {
                elems.push(i);
                heap.push(j);
            }
        }

        check(&mut heap, elems);
    }

    #[test]
    /// Tests merging with the left hand side already with the minimum node
    fn merge_left() {
        const N: usize = 200;

        let (mut even, mut odds): (Heap<_>, Heap<_>) = (0..N).partition(|i| i % 2 == 0);
        even.merge(&mut odds);

        check(&mut even, 0..N);
        check(&mut odds, 0..0);
    }

    #[test]
    /// Tests merging with the left hand side already with the minimum node
    fn merge_right() {
        const N: usize = 200;

        let (mut even, mut odds): (Heap<_>, Heap<_>) = (0..N).partition(|i| i % 2 == 0);
        odds.merge(&mut even);

        check(&mut even, 0..0);
        check(&mut odds, 0..N);
    }

    #[test]
    /// Tests merging with the left hand side already with the minimum node
    fn merge_right_empty() {
        const N: usize = 100;

        let mut heap: Heap<_> = (0..N).collect();
        let mut empty = Heap::new();
        heap.merge(&mut empty);

        check(&mut heap, 0..N);
        check(&mut empty, 0..0);
    }

    #[test]
    /// Tests merging with the left hand side already with the minimum node
    fn merge_left_empty() {
        const N: usize = 100;

        let mut heap: Heap<_> = (0..N).collect();
        let mut empty = Heap::new();
        empty.merge(&mut heap);

        check(&mut empty, 0..N);
        check(&mut heap, 0..0);
    }
}

