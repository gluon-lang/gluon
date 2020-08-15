use std::iter::FusedIterator;

pub fn merge3<F, A: ?Sized, B: ?Sized, C: ?Sized, R>(
    a_original: &A,
    a: Option<A::Owned>,
    b_original: &B,
    b: Option<B::Owned>,
    c_original: &C,
    c: Option<C::Owned>,
    f: F,
) -> Option<R>
where
    A: ToOwned,
    B: ToOwned,
    C: ToOwned,
    F: FnOnce(A::Owned, B::Owned, C::Owned) -> R,
{
    let a_b = merge(a_original, a, b_original, b, |a, b| (a, b));
    merge_fn(
        &(a_original, b_original),
        |_| (a_original.to_owned(), b_original.to_owned()),
        a_b,
        c_original,
        C::to_owned,
        c,
        |(a, b), c| f(a, b, c),
    )
}

/// Merges two values using `f` if either or both them is `Some(..)`.
/// If both are `None`, `None` is returned.
pub fn merge<F, A: ?Sized, B: ?Sized, R>(
    a_original: &A,
    a: Option<A::Owned>,
    b_original: &B,
    b: Option<B::Owned>,
    f: F,
) -> Option<R>
where
    A: ToOwned,
    B: ToOwned,
    F: FnOnce(A::Owned, B::Owned) -> R,
{
    merge_fn(a_original, A::to_owned, a, b_original, B::to_owned, b, f)
}

pub fn merge_fn<'a, 'b, F, G, H, A: ?Sized, B: ?Sized, A1, B1, R>(
    a_original: &'a A,
    g: G,
    a: Option<A1>,
    b_original: &'b B,
    h: H,
    b: Option<B1>,
    merger: F,
) -> Option<R>
where
    F: FnOnce(A1, B1) -> R,
    G: FnOnce(&'a A) -> A1,
    H: FnOnce(&'b B) -> B1,
{
    match (a, b) {
        (Some(a), Some(b)) => Some(merger(a, b)),
        (Some(a), None) => Some(merger(a, h(b_original))),
        (None, Some(b)) => Some(merger(g(a_original), b)),
        (None, None) => None,
    }
}

pub fn merge_tuple_iter<'a, I, F, T, R>(types: I, mut f: F) -> Option<R>
where
    I: IntoIterator<Item = (&'a T, &'a T)>,
    I::IntoIter: FusedIterator + Clone,
    F: FnMut(&'a T, &'a T) -> Option<T>,
    T: Clone + 'a,
    R: std::iter::FromIterator<T>,
{
    merge_collect(&mut (), types, |_, (l, r)| f(l, r), |_, (l, _)| l.clone())
}

pub struct MergeIter<'s, I, F, G, T, S>
where
    S: ?Sized,
{
    types: I,
    clone_types_iter: I,
    action: F,
    converter: G,
    clone_types: usize,
    next: Option<T>,
    pub state: &'s mut S,
}

impl<'s, I, F, G, U, S> Iterator for MergeIter<'s, I, F, G, U, S>
where
    S: ?Sized,
    I: Iterator,
    F: FnMut(&mut S, I::Item) -> Option<U>,
    G: FnMut(&mut S, I::Item) -> U,
{
    type Item = U;
    fn next(&mut self) -> Option<Self::Item> {
        if self.clone_types > 0 {
            self.clone_types -= 1;
            let converter = &mut self.converter;
            let state = &mut self.state;
            self.clone_types_iter.next().map(|e| converter(state, e))
        } else if let Some(typ) = self.next.take() {
            self.clone_types_iter.next();
            Some(typ)
        } else {
            let action = &mut self.action;
            let state = &mut self.state;

            if let Some((i, typ)) = self
                .types
                .by_ref()
                .enumerate()
                .find_map(|(i, typ)| action(state, typ).map(|typ| (i, typ)))
            {
                self.clone_types = i;
                self.next = Some(typ);
                self.next()
            } else {
                self.clone_types = usize::max_value();
                self.next()
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.clone_types_iter.size_hint()
    }
}

impl<I, F, G, U, S> ExactSizeIterator for MergeIter<'_, I, F, G, U, S>
where
    S: ?Sized,
    I: ExactSizeIterator,
    F: FnMut(&mut S, I::Item) -> Option<U>,
    G: FnMut(&mut S, I::Item) -> U,
{
    fn len(&self) -> usize {
        self.clone_types_iter.len()
    }
}

pub fn merge_collect<I, F, G, U, S, R>(
    state: &mut S,
    types: I,
    action: F,
    converter: G,
) -> Option<R>
where
    S: ?Sized,
    I: IntoIterator,
    I::IntoIter: FusedIterator + Clone,
    F: FnMut(&mut S, I::Item) -> Option<U>,
    G: FnMut(&mut S, I::Item) -> U,
    R: std::iter::FromIterator<U>,
{
    merge_iter(state, types, action, converter).map(|iter| iter.collect())
}

pub fn merge_iter<I, F, G, U, S>(
    state: &mut S,
    types: I,
    mut action: F,
    converter: G,
) -> Option<MergeIter<'_, I::IntoIter, F, G, U, S>>
where
    S: ?Sized,
    I: IntoIterator,
    I::IntoIter: FusedIterator + Clone,
    F: FnMut(&mut S, I::Item) -> Option<U>,
    G: FnMut(&mut S, I::Item) -> U,
{
    let mut types = types.into_iter();
    let clone_types_iter = types.clone();
    if let Some((i, typ)) = types
        .by_ref()
        .enumerate()
        .find_map(|(i, typ)| action(state, typ).map(|typ| (i, typ)))
    {
        Some(MergeIter {
            clone_types_iter,
            types,
            action,
            converter,
            clone_types: i,
            next: Some(typ),
            state,
        })
    } else {
        None
    }
}
