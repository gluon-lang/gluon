//! Module containing bindings to rust's `std::time` module.

use crate::real_std::{
    time,
    convert::TryInto,
};

use crate::vm::{
    self,
    api::{RuntimeResult, IO},
    thread::Thread,
    types::VmInt,
    ExternModule,
};

mod duration {
    use super::*;

    #[derive(Clone, Debug, Userdata, Trace, VmType)]
    #[gluon_userdata(clone)]
    #[gluon(vm_type = "std.time.types.Duration")]
    #[gluon(crate_name = "::vm")]
    #[gluon_trace(skip)]
    pub(crate) struct Duration(pub(crate) time::Duration);

    pub(crate) fn as_secs(dur: &Duration) -> RuntimeResult<VmInt, String> {
        dur.0.as_secs()
            .try_into()
            .map_err(|_| String::from("Overflow when trying to convert Duration into seconds"))
            .into()
    }

    pub(crate) fn subsec_nanos(dur: &Duration) -> VmInt {
        dur.0.subsec_nanos() as VmInt
    }
}

mod instant {
    use super::{ *, duration::Duration };

    #[derive(Clone, Debug, Userdata, Trace, VmType)]
    #[gluon_userdata(clone)]
    #[gluon(vm_type = "std.time.types.Instant")]
    #[gluon(crate_name = "::vm")]
    #[gluon_trace(skip)]
    pub(crate) struct Instant(pub(crate) time::Instant);

    pub(crate) fn now(_: ()) -> IO<Instant> {
        IO::Value(Instant(time::Instant::now()))
    }

    /// Returns `Some(later - earlier)` if `later` is the same as or later than `earlier`.
    /// Returns None otherwise.
    pub(crate) fn duration_since(later: &Instant, earlier: &Instant) -> Option<Duration> {
        // Note: replace with checked_duration_since when 1.38 is stable
        if later.0 >= earlier.0 {
            // should never panic
            Some(Duration(later.0.duration_since(earlier.0)))
        } else {
            None
        }
    }

    pub(crate) fn elapsed(earlier: &Instant) -> Duration {
        Duration(earlier.0.elapsed())
    }
}

mod system_time {
    use super::{ *, duration::Duration };

    #[derive(Clone, Debug, Userdata, Trace, VmType)]
    #[gluon_userdata(clone)]
    #[gluon(vm_type = "std.time.types.SystemTime")]
    #[gluon(crate_name = "::vm")]
    #[gluon_trace(skip)]
    pub(crate) struct SystemTime(pub(crate) time::SystemTime);

    pub(crate) fn now(_: ()) -> IO<SystemTime> {
        IO::Value(SystemTime(time::SystemTime::now()))
    }

    /// Returns `Ok(later - earlier)` if `later` is the same as or later than `earlier`.
    /// Returns `Err(earlier - later)` if `later` is earlier than `earlier`.
    pub(crate) fn duration_since(later : &SystemTime, earlier : &SystemTime) -> Result<Duration, Duration> {
        later.0.duration_since(earlier.0)
            .map(|x| Duration(x))
            .map_err(|e| Duration(e.duration()))
    }

    pub(crate) fn elapsed(earlier: &SystemTime) -> Result<Duration, Duration> {
        earlier.0.elapsed()
            .map(|x| Duration(x))
            .map_err(|e| Duration(e.duration()))
    }
}

mod std {
    pub mod time {
        pub use crate::std_lib::time as prim;
    }
}

pub fn load(vm: &Thread) -> vm::Result<ExternModule> {
    vm.register_type::<duration::Duration>("std.time.types.Duration", &[])?;
    vm.register_type::<instant::Instant>("std.time.types.Instant", &[])?;
    vm.register_type::<system_time::SystemTime>("std.time.types.SystemTime", &[])?;

    ExternModule::new(
        vm,
        record! {
            duration => record! {
                type std::time::Duration => duration::Duration,

                as_secs => primitive!(1, std::time::prim::duration::as_secs),
                subsec_nanos => primitive!(1, std::time::prim::duration::subsec_nanos),
            },
            instant => record! {
                type std::time::Instant => instant::Instant,

                now => primitive!(1, std::time::prim::instant::now),
                duration_since => primitive!(2, std::time::prim::instant::duration_since),
                elapsed => primitive!(1, std::time::prim::instant::elapsed),
            },
            system_time => record! {
                type std::time::SystemTime => system_time::SystemTime,

                unix_epoch => system_time::SystemTime(time::UNIX_EPOCH),

                now => primitive!(1, std::time::prim::system_time::now),
                duration_since => primitive!(2, std::time::prim::system_time::duration_since),
                elapsed => primitive!(1, std::time::prim::system_time::elapsed),
            },
        }
    )
}
