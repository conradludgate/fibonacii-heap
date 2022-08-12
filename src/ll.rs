//! The core data structures of fibonacii-heap.
//! Includes a [`LinkedListTree`] and [`Node`] type.
//!
//! This differs from [`std::collections::LinkedList`] because
//! [`Node`] contains children as a sub-linked list.

use std::{marker::PhantomData, mem, ptr::NonNull};

pub struct Node<T> {
    children: LinkedListTree<T>,
    // unused atm, for decrease_key
    _marked: bool,

    next: Option<NonNull<Node<T>>>,
    prev: Option<NonNull<Node<T>>>,

    element: T,
}

impl<T: Ord> Node<T> {
    pub const fn new(t: T) -> Self {
        Self {
            children: LinkedListTree::new(),
            _marked: false,
            element: t,
            next: None,
            prev: None,
        }
    }

    pub fn degree(&self) -> usize {
        self.children.len()
    }

    /// Merges two nodes, preserving the minimum-heap property
    pub fn merge(&mut self, mut other: Box<Self>) {
        if self.element > other.element {
            std::mem::swap(self, &mut other);
        }
        self.children.push_back_node(other);
    }

    pub fn into_inner(self) -> T {
        self.element
    }

    pub fn get(&self) -> &T {
        &self.element
    }
}

pub struct LinkedListTree<T> {
    head: Option<NonNull<Node<T>>>,
    tail: Option<NonNull<Node<T>>>,
    len: usize,
    marker: PhantomData<Box<Node<T>>>,
}

impl<T> Default for LinkedListTree<T> {
    fn default() -> Self {
        Self {
            head: Default::default(),
            tail: Default::default(),
            len: Default::default(),
            marker: Default::default(),
        }
    }
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
        self.append(&mut other.children)
    }

    /// Adds the given node to the back of the list.
    pub fn push_back_node(&mut self, mut node: Box<Node<T>>) -> Option<NonNull<Node<T>>> {
        // This method takes care not to create mutable references to whole nodes,
        // to maintain validity of aliasing pointers into `element`.
        unsafe {
            node.next = None;
            node.prev = self.tail;
            let node = Some(Box::leak(node).into());

            match self.tail {
                None => self.head = node,
                // Not creating new mutable (unique!) references overlapping `element`.
                Some(tail) => (*tail.as_ptr()).next = node,
            }

            self.tail = node;
            self.len += 1;

            node
        }
    }

    fn pop_front_node(&mut self) -> Option<Box<Node<T>>> {
        // This method takes care not to create mutable references to whole nodes,
        // to maintain validity of aliasing pointers into `element`.
        self.head.map(|node| unsafe {
            let node = Box::from_raw(node.as_ptr());
            self.head = node.next;

            match self.head {
                None => self.tail = None,
                // Not creating new mutable (unique!) references overlapping `element`.
                Some(head) => (*head.as_ptr()).prev = None,
            }

            self.len -= 1;
            node
        })
    }

    /// removes the node from the linked list
    ///
    /// # Safety
    ///
    /// node must be an element within the linked list
    pub unsafe fn remove_node(&mut self, node: NonNull<Node<T>>) -> Box<Node<T>> {
        self.unlink_node(node);
        Box::from_raw(node.as_ptr())
    }

    /// Provides a cursor with editing operations at the front element.
    ///
    /// The cursor is pointing to the "ghost" non-element if the list is empty.
    pub fn cursor_front_mut(&mut self) -> CursorMut<'_, T> {
        CursorMut {
            current: self.head,
            list: self,
        }
    }

    /// Unlinks the specified node from the current list.
    ///
    /// Warning: this will not check that the provided node belongs to the current list.
    ///
    /// This method takes care not to create mutable references to `element`, to
    /// maintain validity of aliasing pointers.
    unsafe fn unlink_node(&mut self, mut node: NonNull<Node<T>>) {
        let node = node.as_mut();

        // Not creating new mutable (unique!) references overlapping `element`.
        match node.prev {
            Some(prev) => (*prev.as_ptr()).next = node.next,
            // this node is the head node
            None => self.head = node.next,
        };

        match node.next {
            Some(next) => (*next.as_ptr()).prev = node.prev,
            // this node is the tail node
            None => self.tail = node.prev,
        };

        self.len -= 1;
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

        while let Some(node) = self.pop_front_node() {
            let guard = DropGuard(self);
            drop(node);
            mem::forget(guard);
        }
    }
}

/// A cursor over a `LinkedList` with editing operations.
///
/// A `Cursor` is like an iterator, except that it can freely seek back-and-forth, and can
/// safely mutate the list during iteration. This is because the lifetime of its yielded
/// references is tied to its own lifetime, instead of just the underlying list. This means
/// cursors cannot yield multiple elements at once.
///
/// Cursors always rest between two elements in the list, and index in a logically circular way.
/// To accommodate this, there is a "ghost" non-element that yields `None` between the head and
/// tail of the list.
pub struct CursorMut<'a, T: 'a> {
    current: Option<NonNull<Node<T>>>,
    list: &'a mut LinkedListTree<T>,
}

impl<'a, T> CursorMut<'a, T> {
    /// Removes the current element from the `LinkedList`.
    ///
    /// The element that was removed is returned, and the cursor is
    /// moved to point to the next element in the `LinkedList`.
    ///
    /// If the cursor is currently pointing to the "ghost" non-element then no element
    /// is removed and `None` is returned.
    pub fn remove_current(&mut self) -> Option<Box<Node<T>>> {
        let unlinked_node = self.current?;
        unsafe {
            self.current = unlinked_node.as_ref().next;
            self.list.unlink_node(unlinked_node);
            let unlinked_node = Box::from_raw(unlinked_node.as_ptr());
            Some(unlinked_node)
        }
    }
}
