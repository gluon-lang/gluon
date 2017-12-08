use futures::{AndThen, Async, Future, Map, MapErr, OrElse, Poll, Then};
use futures::future::{Either, FutureResult};

use Error;

/// `FutureValue` holds either an already computed value or a `Future` which can be resolved into
/// that value. This makes it possible to avoid creating an event loop for computions which run
/// synchronously.
pub enum FutureValue<F>
where
    F: Future,
{
    Value(Result<F::Item, F::Error>),
    Future(F),
    Polled,
}

pub type BoxFutureValue<'a, T, E> = FutureValue<Box<Future<Item = T, Error = E> + Send + 'a>>;

impl<F> FutureValue<F>
where
    F: Future,
    F::Error: From<Error>,
{
    /// Returns the resolved `value` if it was synchronously computed or an error otherwise
    pub fn sync_or_error(self) -> Result<F::Item, F::Error> {
        match self {
            FutureValue::Value(v) => v,
            FutureValue::Future(_) => {
                Err(Error::Message("Future needs to be resolved asynchronously".into()).into())
            }
            FutureValue::Polled => {
                ice!("`FutureValue` may not be polled again if it contained a value")
            }
        }
    }
}

impl<T, E> From<Result<T, E>> for FutureValue<FutureResult<T, E>> {
    fn from(result: Result<T, E>) -> FutureValue<FutureResult<T, E>> {
        FutureValue::Value(result)
    }
}

impl<T, E> FutureValue<FutureResult<T, E>> {
    pub fn sync(result: Result<T, E>) -> FutureValue<FutureResult<T, E>> {
        FutureValue::Value(result)
    }
}

impl<'f, F> FutureValue<F>
where
    F: Future + 'f,
{
    pub fn boxed(self) -> FutureValue<Box<Future<Item = F::Item, Error = F::Error> + Send + 'f>>
    where
        F: Send,
    {
        match self {
            FutureValue::Value(v) => FutureValue::Value(v),
            FutureValue::Future(f) => FutureValue::Future(Box::new(f)),
            FutureValue::Polled => FutureValue::Polled,
        }
    }

    pub fn map<G, U>(self, g: G) -> FutureValue<Map<F, G>>
    where
        G: FnOnce(F::Item) -> U,
    {
        match self {
            FutureValue::Value(v) => FutureValue::Value(v.map(g)),
            FutureValue::Future(f) => FutureValue::Future(f.map(g)),
            FutureValue::Polled => FutureValue::Polled,
        }
    }

    pub fn map_err<G, U>(self, g: G) -> FutureValue<MapErr<F, G>>
    where
        G: FnOnce(F::Error) -> U,
    {
        match self {
            FutureValue::Value(v) => FutureValue::Value(v.map_err(g)),
            FutureValue::Future(f) => FutureValue::Future(f.map_err(g)),
            FutureValue::Polled => FutureValue::Polled,
        }
    }

    pub fn and_then<G, B>(self, g: G) -> FutureValue<Either<B, AndThen<F, FutureValue<B>, G>>>
    where
        G: FnOnce(F::Item) -> FutureValue<B>,
        B: Future<Error = F::Error>,
    {
        match self {
            FutureValue::Value(v) => match v {
                Ok(v) => match g(v) {
                    FutureValue::Value(v) => FutureValue::Value(v),
                    FutureValue::Future(f) => FutureValue::Future(Either::A(f)),
                    FutureValue::Polled => FutureValue::Polled,
                },
                Err(err) => FutureValue::Value(Err(err)),
            },
            FutureValue::Future(f) => FutureValue::Future(Either::B(f.and_then(g))),
            FutureValue::Polled => FutureValue::Polled,
        }
    }

    pub fn then<G, B>(self, g: G) -> FutureValue<Either<B, Then<F, FutureValue<B>, G>>>
    where
        G: FnOnce(Result<F::Item, F::Error>) -> FutureValue<B>,
        B: Future,
    {
        match self {
            FutureValue::Value(v) => match g(v) {
                FutureValue::Value(v) => FutureValue::Value(v),
                FutureValue::Future(f) => FutureValue::Future(Either::A(f)),
                FutureValue::Polled => FutureValue::Polled,
            },
            FutureValue::Future(f) => FutureValue::Future(Either::B(f.then(g))),
            FutureValue::Polled => FutureValue::Polled,
        }
    }

    pub fn or_else<G, B>(self, g: G) -> FutureValue<Either<B, OrElse<F, FutureValue<B>, G>>>
    where
        G: FnOnce(F::Error) -> FutureValue<B>,
        B: Future<Item = F::Item>,
    {
        match self {
            FutureValue::Value(v) => match v {
                Ok(v) => FutureValue::Value(Ok(v)),
                Err(err) => match g(err) {
                    FutureValue::Value(v) => FutureValue::Value(v),
                    FutureValue::Future(f) => FutureValue::Future(Either::A(f)),
                    FutureValue::Polled => FutureValue::Polled,
                },
            },
            FutureValue::Future(f) => FutureValue::Future(Either::B(f.or_else(g))),
            FutureValue::Polled => FutureValue::Polled,
        }
    }
}

impl<F> Future for FutureValue<F>
where
    F: Future,
{
    type Item = F::Item;
    type Error = F::Error;

    fn poll(&mut self) -> Poll<F::Item, F::Error> {
        match *self {
            FutureValue::Value(_) => match ::std::mem::replace(self, FutureValue::Polled) {
                FutureValue::Value(v) => return v.map(Async::Ready),
                _ => unreachable!(),
            },
            FutureValue::Future(ref mut f) => f.poll(),
            FutureValue::Polled => {
                ice!("`FutureValue` may not be polled again if it contained a value")
            }
        }
    }

    fn wait(self) -> Result<F::Item, F::Error> {
        match self {
            FutureValue::Value(v) => v,
            FutureValue::Future(f) => f.wait(),
            FutureValue::Polled => {
                ice!("`FutureValue` may not be polled again if it contained a value")
            }
        }
    }
}

#[macro_export]
macro_rules! try_future {
    ($e: expr) => {
        match $e {
            Ok(ok) => ok,
            Err(err) => return $crate::future::FutureValue::Value(Err(err.into())),
        }
    }
}
