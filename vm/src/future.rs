use futures::{Async, Future, Poll};

use Error;

/// `FutureValue` holds either an already computed value or a `Future` which can be resolved into
/// that value. This makes it possible to avoid creating an event loop for computions which run
/// synchronously.
pub enum FutureValue<F>
    where F: Future,
{
    Value(F::Item),
    Future(F),
    Polled,
}

impl<F> FutureValue<F>
    where F: Future<Error = Error>,
{
    /// Returns the resolved `value` if it was synchronously computed or an error otherwise
    pub fn sync_or_error(self) -> Result<F::Item, Error> {
        match self {
            FutureValue::Value(v) => Ok(v),
            FutureValue::Future(_) => {
                Err(Error::Message("Future needs to be resolved asynchronously".into()))
            }
            FutureValue::Polled => {
                panic!("`FutureValue` may not be polled again if it contained a value")
            }
        }
    }
}

impl<F> Future for FutureValue<F>
    where F: Future,
{
    type Item = F::Item;
    type Error = F::Error;

    fn poll(&mut self) -> Poll<F::Item, F::Error> {
        match *self {
            FutureValue::Value(_) => {
                match ::std::mem::replace(self, FutureValue::Polled) {
                    FutureValue::Value(v) => return Ok(Async::Ready(v)),
                    _ => unreachable!(),
                }
            }
            FutureValue::Future(ref mut f) => f.poll(),
            FutureValue::Polled => {
                panic!("`FutureValue` may not be polled again if it contained a value")
            }
        }
    }

    fn wait(self) -> Result<F::Item, F::Error> {
        match self {
            FutureValue::Value(v) => Ok(v),
            FutureValue::Future(f) => f.wait(),
            FutureValue::Polled => {
                panic!("`FutureValue` may not be polled again if it contained a value")
            }
        }
    }
}
