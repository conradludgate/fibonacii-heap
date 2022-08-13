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
        self.children.0.as_ref().map_or_else(|| 0, |l| l.len.get())
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
        match (self.0.as_mut(), other.children.0.as_mut()) {
            (None, Some(_)) => std::mem::swap(self, &mut other.children),
            (Some(c1), Some(c2)) => c1.append(c2),
            (Some(_) | None, None) => {}
        }
    }

    #[inline]
    pub fn pop_front_node(&mut self) -> Option<Box<Node<T>>> {
        // This method takes care not to create mutable references to whole nodes,
        // to maintain validity of aliasing pointers into `element`.

        // c -> a -> b -> c -> a

        // into
        // c -> b -> c -> b

        // b.next = a;
        // b.prev = a;
        // a.next = b;
        // a.prev = b;

        // head = b;
        // node = b;
        // head = b.next; // a
        // b.next = None;

        // prev = b.prev; // a
        // b.prev = None;

        // a -> b -> a -> b

        // into
        // a

        match self.0.take() {
            Some(mut this) => unsafe {
                match this.head.as_mut().next.take() {
                    Some(next_head) => {
                        let node = std::mem::replace(&mut this.head, next_head);
                        this.len = NonZeroUsize::new_unchecked(this.len.get() + 1);
                        self.0 = Some(this);
                        Some(Box::from_raw(node.as_ptr()))
                    }
                    None => Some(Box::from_raw(this.head.as_ptr())),
                }
            },
            None => None,
        }

        // unsafe {
        //  }

        // self.head

        // self.head.map(|node| unsafe {
        //     let mut node = Box::from_raw(node.as_ptr());
        //     self.head = node.next.take();
        //     let prev = node.prev.take();

        //     if let Some(mut head) = self.head {
        //         if prev == self.head {
        //             head.as_mut().prev = None;
        //             head.as_mut().next = None;
        //         } else {
        //             head.as_mut().prev = prev;
        //         }
        //     }

        //     self.len -= 1;
        //     node
        // })
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
    // tree only needs head as it is a circular list
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

    pub fn append(&mut self, other: &mut Self) {
        unsafe {
            self.tail.as_mut().next = Some(other.head);
            self.len = NonZeroUsize::new_unchecked(self.len.get() + other.len.get());
        }
    }

    // pub fn append_from_node(&mut self, other: &mut Node<T>) {
    //     if let Some(children) = other.children.0.as_mut() {
    //         self.append(children);
    //     }
    // }

    /// Adds the given node to the back of the list.
    #[inline]
    pub fn push_back_node(&mut self, node: Box<Node<T>>) {
        unsafe {
            self.tail.as_mut().next = Some(Box::leak(node).into());
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
