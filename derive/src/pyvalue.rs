use proc_macro2::TokenStream;
use quote::{quote, ToTokens};
use syn::{Data, DeriveInput, Result};

pub(crate) fn impl_pyvalue(input: DeriveInput) -> Result<TokenStream> {
    let ty = &input.ident;

    let make_field_offset = |name, typ, i, field: &syn::Field| {
        let fieldname = match field.ident.as_ref() {
            Some(id) => id.to_token_stream(),
            None => syn::Index::from(i).into_token_stream(),
        };
        quote! {
            const #name: ::core::option::Option<
                ::rustpython_vm::common::field_offset::FieldOffset<Self, #typ>,
            > = ::core::option::Option::Some(
                ::rustpython_vm::common::field_offset!(Self, #fieldname),
            );
        }
    };

    let mut dict_field = None;
    let mut weaklist_field = None;
    if let Data::Struct(struc) = &input.data {
        for (i, field) in struc.fields.iter().enumerate() {
            for attr in &field.attrs {
                if attr.path.is_ident("dict") {
                    if dict_field.is_some() {
                        bail_span!(attr, "already have a dict member")
                    }
                    dict_field = Some(make_field_offset(
                        quote!(DICT),
                        quote!(::rustpython_vm::InstanceDict),
                        i,
                        field,
                    ));
                } else if attr.path.is_ident("weaklist") {
                    if weaklist_field.is_some() {
                        bail_span!(attr, "already have a weaklist member")
                    }
                    weaklist_field = Some(make_field_offset(
                        quote!(WEAKREFLIST),
                        quote!(::rustpython_vm::WeakRefList),
                        i,
                        field,
                    ));
                }
            }
        }
    }

    let ret = quote! {
        impl ::rustpython_vm::PyValue for #ty {
            fn class(_vm: &::rustpython_vm::VirtualMachine) -> &rustpython_vm::builtins::PyTypeRef {
                <Self as ::rustpython_vm::StaticType>::static_type()
            }

            #dict_field
            #weaklist_field
        }
    };
    Ok(ret)
}
