use std::ptr::NonNull;

mod ll;

pub struct Heap<T> {
    children: ll::LinkedListTree<T>,
    minimum: Option<NonNull<ll::Node<T>>>,
    scratch: Scratch<Box<ll::Node<T>>>,
}
impl<T> Default for Heap<T> {
    fn default() -> Self {
        Self {
            children: Default::default(),
            minimum: Default::default(),
            scratch: Default::default(),
        }
    }
}

struct Scratch<T> {
    space: Vec<Option<T>>,
}
impl<T> Default for Scratch<T> {
    fn default() -> Self {
        Self {
            space: Default::default(),
        }
    }
}

impl<T> Scratch<T> {
    fn space(&mut self, d: usize) -> &mut Option<T> {
        // fill in the space if not large enough
        if d >= self.space.len() {
            self.space.resize_with(d + 1, || None);
        }
        &mut self.space[d]
    }
}

impl<T: Ord> Heap<T> {
    /// Get a reference to the highest priority entry in the heap if it exists. O(1)
    pub fn first(&self) -> Option<&T> {
        self.minimum.map(|p| {
            // SAFETY: We have shared ref of the entire heap -
            // so we know that no one is mutating this pointer
            unsafe { (*p.as_ptr()).get() }
        })
    }

    /// Insert a new entry into the heap. O(1)
    pub fn insert(&mut self, t: T) {
        self.insert_node(Box::new(ll::Node::new(t)));
    }

    fn insert_node(&mut self, node: Box<ll::Node<T>>) {
        match self.first() {
            Some(min) if min <= node.get() => { /* already have the minimum */ }
            _ => self.minimum = Some(node.as_ref().into()),
        }
        self.children.push_back_node(node);
    }

    /// Moves all the elements of `other` into `self`, leaving `other` empty.
    pub fn merge(&mut self, other: &mut Self) {
        match (self.first(), other.first()) {
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
            heap.insert(i);
        }
        assert_eq!(heap.first(), Some(&0));
        assert_eq!(heap.pop(), Some(0));

        for i in 1..100 {
            assert_eq!(heap.pop(), Some(i));
        }
    }
}
