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

use std::{num::NonZeroUsize, ptr::NonNull};

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
    minimum: Option<NonNull<ll::Node<T>>>,
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
impl<T> Default for Scratch<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Scratch<T> {
    const fn new() -> Self {
        Self { space: Vec::new() }
    }

    fn reserve(&mut self, n: NonZeroUsize) {
        // A heap with `n` elements should have max-degree log2(n)+1.
        // This quantity can break if we get unlucky and remove only the small
        // degree nodes and leave large degree nodes unchecked.
        // This isn't a problem here though since we never decrease the space
        let new_len = (usize::BITS - n.leading_zeros()) as usize;
        if new_len > self.space.len() {
            self.space.resize_with(new_len, || None);
        }
    }

    fn space(&mut self, d: usize) -> &mut Option<T> {
        // Safety: space is guaranteed to be available (see reserve)
        unsafe { self.space.get_unchecked_mut(d) }
    }
}

impl<T> Heap<T> {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            children: ll::LinkedListTree::new(),
            minimum: None,
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
        self.minimum.map(|p| {
            // SAFETY: We have shared ref of the entire heap -
            // so we know that no one is mutating this pointer
            unsafe { p.as_ref().get() }
        })
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
        self.len += 1;
        // Safety: we just incremented it by 1 so we know it's >0
        let len = unsafe { NonZeroUsize::new_unchecked(self.len) };
        self.scratch.reserve(len);
        self.insert_node(Box::new(ll::Node::new(t)));
    }

    fn insert_node(&mut self, node: Box<ll::Node<T>>) {
        // Note: we don't increment the length here, since this is also used when reinserting deep nested nodes
        let new_min = !matches!(self.peek(), Some(min) if min <= node.get());
        let node = self.children.push_back_node(node);
        if new_min {
            self.minimum = Some(node);
        }
    }

    /// Moves all the elements of `other` into `self`, leaving `other` empty.
    ///
    /// # Time complexity
    ///
    /// Cost is *O*(1) in the worst case.
    pub fn merge(&mut self, other: &mut Self) {
        match (self.peek(), other.peek()) {
            (Some(x), Some(y)) => {
                // swap so self is the minimum heap
                if x > y {
                    std::mem::swap(self, other);
                }
                self.children.append(&mut other.children);

                self.len += other.len;
                // Safety: we just incremented so we know it's >0
                let len = unsafe { NonZeroUsize::new_unchecked(self.len) };
                self.scratch.reserve(len);

                other.len = 0;
                other.minimum = None;
            }
            // if other has values but self does not,
            // swap the whole heaps to make other empty as promised.
            (None, Some(_)) => std::mem::swap(self, other),
            // other is already drained
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
        Some(value)
    }

    fn phase1(&mut self) -> Option<Box<ll::Node<T>>> {
        match self.minimum.take() {
            Some(min) => {
                // SAFETY: minimum is guaranteed to be within the linked list
                let mut value = unsafe { self.children.remove_node(min) };
                self.len -= 1;

                self.children.append_from_node(&mut value);

                debug_assert_eq!(value.degree(), 0);

                Some(value)
            }
            None => None,
        }
    }

    fn phase2(&mut self) {
        while let Some(mut current) = self.children.pop_front_node() {
            loop {
                let d = self.scratch.space(current.degree());

                // if we have a duplicate degree, then remove and merge
                // else store the current node at that degree
                if let Some(v) = d.take() {
                    current.merge(v);
                } else {
                    *d = Some(current);
                    break;
                }
            }
        }

        debug_assert!(self.children.is_empty());
    }

    fn phase3(&mut self) {
        let mut iter = self.scratch.space.iter_mut().filter_map(Option::take);

        if let Some(node) = iter.next() {
            let mut min = self.children.push_back_node(node);
            for node in iter {
                let first = unsafe { min.as_ref().get() };
                let new_min = first > node.get();
                let node = self.children.push_back_node(node);
                if new_min {
                    min = node;
                }
            }
            self.minimum = Some(min);
        };

        debug_assert_eq!(self.scratch.space.iter().flatten().count(), 0);
    }
}

#[cfg(test)]
mod tests {
    use rand::{seq::SliceRandom, thread_rng};

    use super::Heap;

    #[test]
    fn works() {
        let mut heap = Heap::default();
        let mut elems: Vec<_> = (0..100).collect();
        elems.shuffle(&mut thread_rng());
        for i in elems {
            heap.push(i);
        }

        for i in 0..100 {
            assert_eq!(heap.peek(), Some(&i));
            assert_eq!(heap.pop(), Some(i));
        }

        assert_eq!(heap.peek(), None);
        assert_eq!(heap.pop(), None);
    }
}
