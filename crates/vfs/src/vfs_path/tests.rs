use super::*;

#[test]
fn vfs_path_is_pointer_sized() {
    assert_eq!(std::mem::size_of::<VfsPath>(), std::mem::size_of::<usize>());
}

#[test]
fn popping_a_clone_does_not_change_the_original() {
    let original = VfsPath::new_virtual_path("/foo/bar".to_owned());
    let mut parent = original.clone();

    assert!(parent.pop());
    assert_eq!(original, VfsPath::new_virtual_path("/foo/bar".to_owned()));
    assert_eq!(parent, VfsPath::new_virtual_path("/foo".to_owned()));
}

#[test]
fn virtual_path_starts_with_is_component_based() {
    let path = |path: &str| VfsPath::new_virtual_path(path.to_owned());

    assert!(!path("/foobar").starts_with(&path("/foo")));
    assert!(path("/foo/bar").starts_with(&path("/foo")));
}

#[test]
fn virtual_path_extensions() {
    assert_eq!(VirtualPath("/".to_owned()).name_and_extension(), None);
    assert_eq!(
        VirtualPath("/directory".to_owned()).name_and_extension(),
        Some(("directory", None))
    );
    assert_eq!(
        VirtualPath("/directory/".to_owned()).name_and_extension(),
        Some(("directory", None))
    );
    assert_eq!(
        VirtualPath("/directory/file".to_owned()).name_and_extension(),
        Some(("file", None))
    );
    assert_eq!(
        VirtualPath("/directory/.file".to_owned()).name_and_extension(),
        Some((".file", None))
    );
    assert_eq!(
        VirtualPath("/directory/.file.rs".to_owned()).name_and_extension(),
        Some((".file", Some("rs")))
    );
    assert_eq!(
        VirtualPath("/directory/file.rs".to_owned()).name_and_extension(),
        Some(("file", Some("rs")))
    );
}
