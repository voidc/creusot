struct IndexVec<T> {
    inner: Vec<T>,
    epoch: Ghost<usize>,
}

struct Index<'a, T> {
    index: usize,
    vec: Ghost<&'a IndexVec<T>>,
    epoch: Ghost<usize>,
}

impl<'a, T> Invariant for Index<'a, T> {
    #[predicate]
    fn invariant(self) -> bool {
        0 <= self.index && self.index < self.vec.len()
    }
}

impl<T> IndexVec<T> {
    fn push(&mut self, e: T) -> Index<'_, T> {
        let index = self.inner.push(e);
        Index { index, vec: Ghost::new(&*self), epoch: self.epoch.clone() }
    }

    #[requires(self.epoch == index.epoch)]
    fn get(&self, index: Index<T, '_>) -> &T {
        self.inner[index]
    }

    fn remove(&mut self, index: Index<T, '_>) {
        self.inner.remove(index);
        self.epoch += 1;
    }
}
