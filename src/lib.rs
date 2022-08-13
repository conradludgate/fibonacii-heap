//! A priority queue implemented with a fibonacii heap.
//!
//! Insertion is *O*(1) and popping the smallest element has *O*(log(*n*)) time complexity.
//! Checking the smallest element is *O*(1).
//!
//! # Examples
//!
//! This is a larger example that implements [Dijkstra's algorithm][dijkstra]
//! to solve the [shortest path problem][sssp] on a [directed graph][dir_graph].
//! It shows how to use [`BinaryHeap`] with custom types.
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

use std::ptr::NonNull;

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
/// be encapsulated to the `BinaryHeap` that observed the logic error and not
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
/// | [push]  | [pop]  | [peek]/[peek\_mut] |
/// |---------|--------|--------------------|
/// | *O*(1) | *O*(1)~ | *O*(1)             |
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

    fn space(&mut self, d: usize) -> &mut Option<T> {
        // fill in the space if not large enough
        if d >= self.space.len() {
            self.space.resize_with(d + 1, || None);
        }
        &mut self.space[d]
    }
}

impl<T> Heap<T> {
    pub const fn new() -> Self {
        Self {
            children: ll::LinkedListTree::new(),
            minimum: None,
            scratch: Scratch::new(),
        }
    }
}

impl<T: Ord> Heap<T> {
    /// Get a reference to the highest priority entry in the heap if it exists. O(1)
    pub fn peek(&self) -> Option<&T> {
        self.minimum.map(|p| {
            // SAFETY: We have shared ref of the entire heap -
            // so we know that no one is mutating this pointer
            unsafe { (*p.as_ptr()).get() }
        })
    }

    /// Get a reference to the highest priority entry in the heap if it exists. O(1)
    pub fn peek_mut(&mut self) -> Option<&mut T> {
        self.minimum.map(|p| {
            // SAFETY: We have shared ref of the entire heap -
            // so we know that no one is mutating this pointer
            unsafe { (*p.as_ptr()).get_mut() }
        })
    }

    /// Insert a new entry into the heap. O(1)
    pub fn push(&mut self, t: T) {
        self.insert_node(Box::new(ll::Node::new(t)));
    }

    fn insert_node(&mut self, node: Box<ll::Node<T>>) {
        let new_min = !matches!(self.peek(), Some(min) if min <= node.get());
        let node = self.children.push_back_node(node);
        if new_min {
            self.minimum = node;
        }
    }

    /// Moves all the elements of `other` into `self`, leaving `other` empty.
    pub fn merge(&mut self, other: &mut Self) {
        match (self.peek(), other.peek()) {
            (Some(x), Some(y)) => {
                // swap so self is the minimum heap
                if x > y {
                    std::mem::swap(self, other);
                }
                self.children.append(&mut other.children);
                other.minimum = None;
            }
            // if other has values but self does not,
            // swap the whole heaps to make other empty as promised.
            (None, Some(_)) => std::mem::swap(self, other),
            // other is already drained
            (Some(_), None) | (None, None) => {}
        }
    }

    /// Remove the highest priority element from the heap. O(1) amortised
    pub fn pop(&mut self) -> Option<T> {
        // SAFETY: minimum is guaranteed to be within the linked list
        let mut value = unsafe { self.children.remove_node(self.minimum?) };
        self.minimum = None;

        // phase 1
        self.children.append_from_node(&mut value);

        debug_assert_eq!(value.degree(), 0);

        // phase 2
        let mut scratch = std::mem::take(&mut self.scratch);

        let mut cursor = self.children.cursor_front_mut();
        while let Some(mut current) = cursor.remove_current() {
            loop {
                let d = scratch.space(current.degree());

                // if we have a duplicate degree, then remove and merge
                // else store the current node at that degree
                match d.take() {
                    Some(v) => current.merge(v),
                    None => {
                        *d = Some(current);
                        break;
                    }
                }
            }
        }

        debug_assert!(self.children.is_empty());

        // phase 3
        for node in scratch.space.drain(..).flatten() {
            self.insert_node(node);
        }

        // put the scratch space back to cache the allocation
        self.scratch = scratch;

        Some(value.into_inner())
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
