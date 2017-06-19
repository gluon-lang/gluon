use smallvec::VecLike;

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
    match (a, b) {
        (Some(a), Some(b)) => Some(f(a, b)),
        (Some(a), None) => Some(f(a, b_original.to_owned())),
        (None, Some(b)) => Some(f(a_original.to_owned(), b)),
        (None, None) => None,
    }
}

pub fn merge_tuple_iter<'a, I, F, T, R>(types: I, mut f: F) -> Option<R>
where
    I: IntoIterator<Item = (&'a T, &'a T)>,
    F: FnMut(&'a T, &'a T) -> Option<T>,
    T: Clone + 'a,
    R: Default + VecLike<T>,
{
    merge_iter(types, |(l, r)| f(l, r), |(l, _)| l.clone())
}

pub fn merge_iter<'a, I, F, G, U, R>(types: I, mut action: F, mut converter: G) -> Option<R>
where
    I: IntoIterator,
    F: FnMut(I::Item) -> Option<U>,
    G: FnMut(I::Item) -> U,
    I::Item: Copy,
    R: Default + VecLike<U>,
{
    let mut out = R::default();
    merge_iter_(
        types.into_iter(),
        false,
        &mut out,
        &mut action,
        &mut converter,
    );
    if out[..].is_empty() {
        None
    } else {
        out[..].reverse();
        Some(out)
    }
}

fn merge_iter_<'a, I, F, G, U, R>(
    mut types: I,
    replaced: bool,
    output: &mut R,
    f: &mut F,
    converter: &mut G,
) where
    I: Iterator,
    F: FnMut(I::Item) -> Option<U>,
    G: FnMut(I::Item) -> U,
    I::Item: Copy,
    R: Default + VecLike<U>,
{
    if let Some(l) = types.next() {
        let new = f(l);
        merge_iter_(types, replaced || new.is_some(), output, f, converter);
        match new {
            Some(typ) => {
                output.push(typ);
            }
            None if replaced || !output[..].is_empty() => {
                output.push(converter(l));
            }
            None => (),
        }
    }
}
