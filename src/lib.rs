#[derive(Debug)]
pub struct Node<T> {
    children: Vec<Node<T>>,
    marked: bool,
    // option used to optimise merges so we can squash in one go. consider switching to a custom LL impl
    value: Option<T>,
}

impl<T: Ord> Node<T> {
    fn degree(&self) -> usize {
        self.children.len()
    }
    fn take(&mut self) -> Self {
        Self {
            children: std::mem::take(&mut self.children),
            marked: std::mem::take(&mut self.marked),
            value: std::mem::take(&mut self.value),
        }
    }

    /// Merges two nodes, preserving the minimum-heap property
    fn merge(&mut self, mut other: Self) {
        if self.value > other.value {
            std::mem::swap(self, &mut other);
        }
        self.children.push(other);
    }
}

#[derive(Default, Debug)]
pub struct Heap<T> {
    children: Vec<Node<T>>,
    minimum: usize,
}

impl<T: Ord> Heap<T> {
    pub fn first(&self) -> Option<&T> {
        self.children
            .get(self.minimum)
            .and_then(|n| n.value.as_ref())
    }

    pub fn insert(&mut self, t: T) {
        if !matches!(self.first(), Some(x) if *x < t) {
            // t is the new minimum node
            self.minimum = self.children.len();
        }
        self.children.push(Node {
            children: Vec::new(),
            marked: false,
            value: Some(t),
        })
    }

    pub fn merge(&mut self, other: &mut Self) {
        match (self.first(), other.first()) {
            (Some(x), Some(y)) => {
                if x > y {
                    std::mem::swap(self, other);
                }
            }
            _ => return,
        }

        self.children.append(&mut other.children);
        other.minimum = 0;
    }

    pub fn pop(&mut self) -> Option<T> {
        if self.children.is_empty() {
            return None;
        }

        let Node {
            mut children,
            value,
            ..
        } = self.children.remove(self.minimum);

        // phase 1
        children.iter_mut().for_each(|c| c.marked = false);
        self.children.append(&mut children);

        // phase 2
        let mut degree = vec![];
        for i in 0..self.children.len() {
            let mut j = i;
            loop {
                let d = self.children[j].degree();
                if d >= degree.len() {
                    degree.resize(d + 1, usize::MAX);
                }
                let k = std::mem::replace(&mut degree[d], usize::MAX);
                if k != usize::MAX {
                    // we have duplicate degrees!
                    let a = self.children[j].take();
                    let b = &mut self.children[k];
                    b.merge(a);
                    if b.value.is_some() {
                        j = k;
                    }
                } else {
                    degree[d] = j;
                    break;
                }
            }
        }
        self.children.retain(|n| n.value.is_some());

        // phase 3
        self.minimum = self
            .children
            .iter()
            .enumerate()
            .min_by_key(|(_, n)| n.value.as_ref().unwrap())
            .map(|(i, _)| i)
            .unwrap_or_default();

        value
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

        for i in &heap.children {
            println!("{} {:?}", i.degree(), i.value);
        }

        for i in 1..100 {
            assert_eq!(heap.pop(), Some(i));
        }
    }
}
