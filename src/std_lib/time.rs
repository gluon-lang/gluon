//! Module containing bindings to rust's `std::time` module.
//!
use crate::real_std::{
    time,
    convert::TryInto,
};

use crate::vm::{
    self,
    api::{Eff, IO},
    thread::Thread,
    types::VmInt,
    ExternModule,
};

#[derive(Clone, Debug, Userdata, Trace, VmType)]
#[gluon(vm_type = "std.time.types.Duration")]
#[gluon(crate_name = "::vm")]
#[gluon_trace(skip)]
struct Duration(time::Duration);

fn as_secs(dur: &Duration) -> VmInt {
    dur.0.as_secs().try_into().expect("Overflow when trying to convert Duration into seconds")
}

fn subsec_nanos(dur: &Duration) -> VmInt {
    dur.0.subsec_nanos() as VmInt
}

#[derive(Clone, Debug, Userdata, Trace, VmType)]
#[gluon(vm_type = "std.time.types.Instant")]
#[gluon(crate_name = "::vm")]
#[gluon_trace(skip)]
struct Instant(time::Instant);

fn instant_now(_: ()) -> IO<Instant> {
    IO::Value(Instant(time::Instant::now()))
}

/// Returns `Some(later - earlier)` if `later` is the same as or later than `earlier`.
/// Returns None otherwise.
fn instant_since(later: &Instant, earlier: &Instant) -> Option<Duration> {
    // Note: replace with checked_duration_since when 1.38 is stable
    if later.0 >= earlier.0 {
        // should never panic
        Some(Duration(later.0.duration_since(earlier.0)))
    } else {
        None
    }
}

fn instant_elapsed(earlier: &Instant) -> Duration {
    Duration(earlier.0.elapsed())
}

#[derive(Clone, Debug, Userdata, Trace, VmType)]
#[gluon(vm_type = "std.time.types.SystemTime")]
#[gluon(crate_name = "::vm")]
#[gluon_trace(skip)]
struct SystemTime(time::SystemTime);

fn system_time_now(_: ()) -> IO<SystemTime> {
    IO::Value(SystemTime(time::SystemTime::now()))
}

/// Returns `Ok(later - earlier)` if `later` is the same as or later than `earlier`.
/// Returns `Err(earlier - later)` if `later` is earlier than `earlier`.
fn system_time_since(later : &SystemTime, earlier : &SystemTime) -> Result<Duration, Duration> {
    later.0.duration_since(earlier.0)
        .map(|x| Duration(x))
        .map_err(|e| Duration(e.duration()))
}

fn system_time_elapsed(earlier: &SystemTime) -> Result<Duration, Duration> {
    earlier.0.elapsed()
        .map(|x| Duration(x))
        .map_err(|e| Duration(e.duration()))
}

mod std {
    pub mod time {
        pub use crate::std_lib::time as prim;
    }
}

pub fn load(vm: &Thread) -> vm::Result<ExternModule> {
    vm.register_type::<Duration>("std.time.types.Duration", &[])?;
    vm.register_type::<Instant>("std.time.types.Instant", &[])?;
    vm.register_type::<SystemTime>("std.time.types.SystemTime", &[])?;

    ExternModule::new(
        vm,
        record! {
            type std::time::Duration => Duration,
            type std::time::Instant => Instant,
            type std::time::SystemTime => SystemTime,

            unix_epoch => SystemTime(time::UNIX_EPOCH),

            as_secs => primitive!(1, std::time::prim::as_secs),
            subsec_nanos => primitive!(1, std::time::prim::subsec_nanos),
            instant_now => primitive!(1, std::time::prim::instant_now),
            instant_since => primitive!(2, std::time::prim::instant_since),
            instant_elapsed => primitive!(1, std::time::prim::instant_elapsed),
            system_time_now => primitive!(1, std::time::prim::system_time_now),
            system_time_since => primitive!(2, std::time::prim::system_time_since),
            system_time_elapsed => primitive!(1, std::time::prim::system_time_elapsed),

        },
    )
}
