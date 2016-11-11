use api::generic::A;
use api::Generic;
use thread::Thread;
use Result;

fn trace(a: Generic<A>) {
    println!("{:?}", a.0);
}

pub fn load(vm: &Thread) -> Result<()> {
    vm.define_global("debug",
                       record!{
        trace => primitive!(1 trace)
    })?;
    Ok(())
}
