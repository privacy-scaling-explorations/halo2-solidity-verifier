use log::{debug, info};
use std::io::ErrorKind::NotFound;
use std::process::Command;
use std::sync::OnceLock;

#[cfg(not(target_arch = "wasm32"))]
static _SOLC_REQUIREMENT: OnceLock<bool> = OnceLock::new();
#[cfg(not(target_arch = "wasm32"))]
/// Checks if `solc` is installed and available in the PATH.
pub fn check_solc_requirement() {
    info!("checking solc installation..");
    _SOLC_REQUIREMENT.get_or_init(|| match Command::new("solc").arg("--version").output() {
        Ok(output) => {
            #[cfg(not(target_arch = "wasm32"))]
            debug!("solc output: {:#?}", output);
            #[cfg(not(target_arch = "wasm32"))]
            debug!("solc output success: {:#?}", output.status.success());
            assert!(
                output.status.success(),
                "`solc` check failed: {}",
                String::from_utf8_lossy(&output.stderr)
            );
            #[cfg(not(target_arch = "wasm32"))]
            debug!("solc check passed, proceeding");
            true
        }
        Err(e) => {
            if let NotFound = e.kind() {
                panic!(
                    "`solc` was not found! Consider using solc-select or check your PATH! {}",
                    e
                );
            } else {
                panic!("`solc` check failed: {}", e);
            }
        }
    });
}
