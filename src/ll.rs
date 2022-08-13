//! The core data structures of fibonacii-heap.
//! Includes a [`LinkedListTree`] and [`Node`] type.
//!
//! This differs from [`std::collections::LinkedList`] because
//! [`Node`] contains children as a sub-linked list.

use std::{marker::PhantomData, mem, ptr::NonNull};

pub struct Node<T> {
    children: LinkedListTree<T>,
    // unused atm, for decrease_key
    // _marked: bool,
    next: Option<NonNull<Node<T>>>,
    prev: Option<NonNull<Node<T>>>,

    element: T,
}

impl<T> Node<T> {
    pub const fn new(t: T) -> Self {
        Self {
            children: LinkedListTree::new(),
            // _marked: false,
            element: t,
            next: None,
            prev: None,
        }
    }

    pub fn degree(&self) -> usize {
        self.children.len()
    }

    pub fn into_inner(self) -> T {
        self.element
    }

    pub fn get(&self) -> &T {
        &self.element
    }
}

impl<T: Ord> Node<T> {
    /// Merges two nodes, preserving the minimum-heap property
    pub fn merge(mut self: Box<Self>, mut other: Box<Self>) -> Box<Self> {
        if self.element > other.element {
            std::mem::swap(&mut self, &mut other);
        }
        self.children.push_back_node(other);
        self
    }
}

pub struct LinkedListTree<T> {
    head: Option<NonNull<Node<T>>>,
    tail: Option<NonNull<Node<T>>>,
    len: usize,
    marker: PhantomData<Box<Node<T>>>,
}

impl<T> LinkedListTree<T> {
    pub const fn new() -> Self {
        LinkedListTree {
            head: None,
            tail: None,
            len: 0,
            marker: PhantomData,
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn first(&self) -> Option<&T> {
        self.head.map(|p| {
            // SAFETY: We have shared ref of the entire heap -
            // so we know that no one is mutating this pointer
            unsafe { p.as_ref().get() }
        })
    }

    pub fn append(&mut self, other: &mut Self) {
        match self.tail {
            None => mem::swap(self, other),
            Some(mut tail) => {
                // `as_mut` is okay here because we have exclusive access to the entirety
                // of both lists.
                if let Some(mut other_head) = other.head.take() {
                    unsafe {
                        tail.as_mut().next = Some(other_head);
                        other_head.as_mut().prev = Some(tail);
                    }

                    self.tail = other.tail.take();
                    self.len += mem::replace(&mut other.len, 0);
                }
            }
        }
    }

    pub fn append_from_node(&mut self, other: &mut Node<T>) {
        self.append(&mut other.children);
    }

    /// Adds the given node to the back of the list.
    #[inline]
    pub fn push_back_node(&mut self, mut node: Box<Node<T>>) {
        // This method takes care not to create mutable references to whole nodes,
        // to maintain validity of aliasing pointers into `element`.
        unsafe {
            node.next = None;
            node.prev = self.tail;
            let node = Some(Box::leak(node).into());

            match self.tail {
                None => self.head = node,
                // Not creating new mutable (unique!) references overlapping `element`.
                Some(mut tail) => tail.as_mut().next = node,
            }

            self.tail = node;
            self.len += 1;
        }
    }

    /// Adds the given node to the front of the list.
    ///
    /// # Safety:
    /// The list must have at least 1 element
    #[inline]
    unsafe fn push_front_node(&mut self, mut node: Box<Node<T>>) {
        debug_assert!(!self.is_empty());

        // This method takes care not to create mutable references to whole nodes,
        // to maintain validity of aliasing pointers into `element`.
        node.next = self.head;
        node.prev = None;
        let node = Box::leak(node).into();

        // Not creating new mutable (unique!) references overlapping `element`.
        self.head.replace(node).unwrap_unchecked().as_mut().prev = Some(node);

        self.len += 1;
    }

    #[inline]
    pub fn pop_front_node(&mut self) -> Option<Box<Node<T>>> {
        // This method takes care not to create mutable references to whole nodes,
        // to maintain validity of aliasing pointers into `element`.
        self.head.map(|node| unsafe {
            let node = Box::from_raw(node.as_ptr());
            self.head = node.next;

            match self.head {
                None => self.tail = None,
                // Not creating new mutable (unique!) references overlapping `element`.
                Some(mut head) => head.as_mut().prev = None,
            }

            self.len -= 1;
            node
        })
    }
}

impl<T: Ord> LinkedListTree<T> {
    /// inserts the node into the linked list. Preserving the min heap proprety
    pub fn insert_node(&mut self, node: Box<Node<T>>) {
        match self.first() {
            // push front if this is the new min
            // safety: list has at least one node
            Some(min) if min > node.get() => unsafe { self.push_front_node(node) },
            // push back if we already have our min
            _ => self.push_back_node(node),
        }
    }
}

impl<T> Drop for LinkedListTree<T> {
    fn drop(&mut self) {
        struct DropGuard<'a, T>(&'a mut LinkedListTree<T>);

        impl<'a, T> Drop for DropGuard<'a, T> {
            fn drop(&mut self) {
                // Continue the same loop we do below. This only runs when a destructor has
                // panicked. If another one panics this will abort.
                while self.0.pop_front_node().is_some() {}
            }
        }

        let guard = DropGuard(self);
        while guard.0.pop_front_node().is_some() {}
        mem::forget(guard);
    }
}

#[cfg(test)]
mod tests {
    use std::{
        collections::LinkedList,
        panic::catch_unwind,
        sync::{atomic::AtomicUsize, Arc},
    };

    #[test]
    fn drop() {
        #[derive(Default, Clone)]
        struct D(Arc<AtomicUsize>);
        impl Drop for D {
            fn drop(&mut self) {
                assert_ne!(
                    self.0.fetch_add(1, std::sync::atomic::Ordering::SeqCst),
                    0,
                    "panic in drop"
                );
            }
        }
        let d = D::default();
        let mut ll = LinkedList::new();
        ll.push_back(d.clone());
        ll.push_back(d.clone());

        catch_unwind(|| std::mem::drop(ll)).unwrap_err();

        // both were still dropped, despite the panic
        assert_eq!(d.0.load(std::sync::atomic::Ordering::SeqCst), 2);
    }
}
