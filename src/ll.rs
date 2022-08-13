//! The core data structures of fibonacii-heap.
//! Includes a [`LinkedListTree`] and [`Node`] type.
//!
//! This differs from [`std::collections::LinkedList`] because
//! [`Node`] contains children as a sub-linked list.

use std::{marker::PhantomData, mem, num::NonZeroUsize, ptr::NonNull};

pub struct Node<T> {
    children: LinkedListTree<T>,
    // unused atm, for decrease_key
    // _marked: bool,
    next: Option<NonNull<Node<T>>>,

    element: T,
}

impl<T> Node<T> {
    pub const fn new(t: T) -> Self {
        Self {
            children: LinkedListTree::new(),
            // _marked: false,
            element: t,
            next: None,
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

pub struct LinkedListTree<T>(pub Option<LinkedListTreeInner<T>>);

impl<T> LinkedListTree<T> {
    pub fn push_back_node(&mut self, node: Box<Node<T>>) {
        match &mut self.0 {
            Some(c) => c.push_back_node(node),
            None => self.0 = Some(LinkedListTreeInner::new(node)),
        }
    }

    pub fn append_from_node(&mut self, other: &mut Node<T>) {
        match (self.0.as_mut(), other.children.0.take()) {
            (None, Some(c)) => self.0 = Some(c),
            (Some(c1), Some(c2)) => c1.append(c2),
            (Some(_) | None, None) => {}
        }
    }

    #[inline]
    pub fn pop_front_node(&mut self) -> Option<Box<Node<T>>> {
        let mut this = self.0.as_mut()?;
        unsafe {
            let mut node = Box::from_raw(this.head.as_ptr());
            match node.next.take() {
                Some(next) => {
                    this.head = next;
                    this.len = NonZeroUsize::new_unchecked(this.len.get() - 1);
                }
                None => self.0 = None,
            }
            Some(node)
        }
    }

    pub const fn new() -> Self {
        Self(None)
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn len(&self) -> usize {
        self.0.as_ref().map_or_else(|| 0, |l| l.len.get())
    }

    pub fn first(&self) -> Option<&T> {
        self.0.as_ref().map(LinkedListTreeInner::first)
    }
}

pub struct LinkedListTreeInner<T> {
    head: NonNull<Node<T>>,
    tail: NonNull<Node<T>>,
    len: NonZeroUsize,
    marker: PhantomData<Box<Node<T>>>,
}

impl<T> LinkedListTreeInner<T> {
    pub fn new(node: Box<Node<T>>) -> Self {
        let node = Box::leak(node).into();
        Self {
            head: node,
            tail: node,
            len: NonZeroUsize::new(1).unwrap(),
            marker: PhantomData,
        }
    }

    pub fn first(&self) -> &T {
        unsafe { self.head.as_ref() }.get()
    }

    // pass by value because we don't want dangling pointers :)
    #[allow(clippy::needless_pass_by_value)]
    pub fn append(&mut self, other: Self) {
        unsafe {
            self.tail.as_mut().next = Some(other.head);
            self.tail = other.tail;
            self.len = NonZeroUsize::new_unchecked(self.len.get() + other.len.get());
        }
    }

    /// Adds the given node to the back of the list.
    #[inline]
    pub fn push_back_node(&mut self, node: Box<Node<T>>) {
        unsafe {
            let node = Box::leak(node).into();
            self.tail.as_mut().next = Some(node);
            self.tail = node;
            self.len = NonZeroUsize::new_unchecked(self.len.get() + 1);
        }
    }

    /// Adds the given node to the front of the list.
    ///
    /// # Safety:
    /// The list must have at least 1 element
    #[inline]
    unsafe fn push_front_node(&mut self, mut node: Box<Node<T>>) {
        node.next = Some(self.head);
        self.head = Box::leak(node).into();
        self.len = NonZeroUsize::new_unchecked(self.len.get() + 1);
    }
}

impl<T: Ord> LinkedListTree<T> {
    /// inserts the node into the linked list. Preserving the min heap proprety
    pub fn insert_node(&mut self, node: Box<Node<T>>) {
        match &mut self.0 {
            Some(c) if c.first() < node.get() => c.push_back_node(node),
            Some(c) => unsafe { c.push_front_node(node) },
            None => self.0 = Some(LinkedListTreeInner::new(node)),
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
        panic::catch_unwind,
        sync::{atomic::AtomicUsize, Arc},
    };

    use crate::ll::{LinkedListTree, LinkedListTreeInner, Node};

    #[test]
    fn drop() {
        #[derive(Default, Clone)]
        struct D(Arc<AtomicUsize>);
        impl Drop for D {
            fn drop(&mut self) {
                assert_ne!(self.0.fetch_add(1, std::sync::atomic::Ordering::SeqCst), 0,);
            }
        }
        let d = D::default();
        let mut ll = LinkedListTree::new();
        ll.push_back_node(Box::new(Node::new(d.clone())));
        ll.push_back_node(Box::new(Node::new(d.clone())));

        catch_unwind(|| std::mem::drop(ll)).unwrap_err();

        // both were still dropped, despite the panic
        assert_eq!(d.0.load(std::sync::atomic::Ordering::SeqCst), 2);
    }

    #[test]
    fn push_pop() {
        let mut ll = LinkedListTree::new();
        ll.push_back_node(Box::new(Node::new(1)));
        ll.push_back_node(Box::new(Node::new(2)));

        assert_eq!(ll.pop_front_node().unwrap().element, 1);
        assert_eq!(ll.pop_front_node().unwrap().element, 2);
        assert!(ll.pop_front_node().is_none());
    }

    #[test]
    fn append() {
        let mut ll1 = LinkedListTree::new();
        ll1.push_back_node(Box::new(Node::new(1)));
        ll1.push_back_node(Box::new(Node::new(2)));

        let mut ll2 = LinkedListTree::new();
        ll2.push_back_node(Box::new(Node::new(3)));
        ll2.push_back_node(Box::new(Node::new(4)));

        ll1.0.as_mut().unwrap().append(ll2.0.take().unwrap());

        assert_eq!(ll1.pop_front_node().unwrap().element, 1);
        assert_eq!(ll1.pop_front_node().unwrap().element, 2);
        assert_eq!(ll1.pop_front_node().unwrap().element, 3);
        assert_eq!(ll1.pop_front_node().unwrap().element, 4);
        assert!(ll1.pop_front_node().is_none());
    }

    #[test]
    fn size() {
        use std::mem::size_of;
        const PTR: usize = size_of::<*const ()>();
        assert_eq!(size_of::<LinkedListTreeInner<()>>(), 3 * PTR);
        assert_eq!(size_of::<LinkedListTree<()>>(), 3 * PTR);
        assert_eq!(size_of::<Node<()>>(), 4 * PTR);
    }
}
