#![feature(proc_macro_diagnostic)]
extern crate syn;
#[macro_use]
extern crate quote;

use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::ToTokens;
use syn::{spanned::Spanned, Ident, ItemEnum, ItemStruct};

/// Automatically implements the [`AstToStr`] trait for the given struct or enum.
/// Every field of the given item must implement [`AstToStr`] or be annotated with one of the
/// the attributes.
///
/// # Example
/// ```ignore
/// ```
#[proc_macro_derive(Trace)]
pub fn derive_trace(input: TokenStream) -> TokenStream {
    let item: syn::Item =
        syn::parse(input).expect("This macro can only be used with structs and enums");

    // TODO: make this configurable
    let crate_path = quote! {
        crate::gc
    };

    let output = match item {
        syn::Item::Struct(i) => generate_struct_impl(i, &crate_path),
        syn::Item::Enum(i) => generate_enum_impl(i, &crate_path),
        _ => {
            item.span()
                .unwrap()
                .error("This macro can only be used with structs and enums");
            return item.into_token_stream().into();
        }
    };

    match output {
        Ok(ok) => ok.into(),
        Err(e) => e.into_compile_error().into(),
    }
}

/// Generates a [`Trace`] impl for the given struct.
fn generate_struct_impl(
    i: ItemStruct,
    crate_path: &TokenStream2,
) -> Result<TokenStream2, syn::Error> {
    let name = i.ident;
    let generics = i.generics;
    let generic_arguments = get_generic_arguments(&generics);
    let fields = i
        .fields
        .iter()
        .enumerate()
        .map(|(i, f)| {
            f.ident
                .clone()
                .map(|i| i.into_token_stream())
                .unwrap_or_else(|| syn::Index::from(i).into_token_stream())
        })
        .collect::<Vec<_>>();
    Ok(quote! {
        unsafe impl #generics #crate_path::Trace for #name #generic_arguments {
            fn trace(&mut self, tracer: &mut dyn FnMut(&mut #crate_path::GcObj)) {
                #( #crate_path::Trace::trace(&mut self.#fields, tracer); )*
            }

            fn after_forwarding(&mut self) {
                #( #crate_path::Trace::after_forwarding(&mut self.#fields); )*
            }
       }
    })
}

/// Generates a [`Trace`] impl for the given enum.
fn generate_enum_impl(e: ItemEnum, crate_path: &TokenStream2) -> Result<TokenStream2, syn::Error> {
    let enum_name = e.ident;
    let mut patterns = Vec::with_capacity(e.variants.len());
    let mut arms = Vec::with_capacity(e.variants.len());
    for var in &e.variants {
        let name = &var.ident;

        let mut fields = Vec::with_capacity(var.fields.len());
        let pattern = {
            let mut index = 0;
            let mut field_bindings = Vec::with_capacity(var.fields.len());

            for f in &var.fields {
                match &f.ident {
                    Some(name) => field_bindings.push(quote! { #name }),
                    None => {
                        let name = Ident::new(&format!("__slot{}", index), f.span());
                        let syn_index = syn::Index::from(index);
                        field_bindings.push(quote! { #syn_index: #name });
                        fields.push(name);
                        index += 1;
                    }
                }
            }

            quote! {
                #enum_name::#name { #(#field_bindings),* }
            }
        };
        patterns.push(pattern);
        arms.push(fields);
    }

    let mut trace_matches = Vec::with_capacity(arms.len());
    let mut forwarding_matches = Vec::with_capacity(arms.len());
    for (pat, fields) in patterns.into_iter().zip(arms.into_iter()) {
        let trace_pat = pat.clone();
        let trace_fields = fields.clone();
        trace_matches.push(quote! {
            #trace_pat => {
                #( #crate_path::Trace::trace(&mut *#trace_fields, tracer); )*
            }
        });
        forwarding_matches.push(quote! {
            #pat => {
                #( #crate_path::Trace::after_forwarding(&mut *#fields); )*
            }
        });
    }

    let generics = e.generics;
    let generic_arguments = get_generic_arguments(&generics);
    Ok(quote! {
        unsafe impl #generics #crate_path::Trace for #enum_name #generic_arguments {
            fn trace(&mut self, tracer: &mut dyn FnMut(&mut #crate_path::GcObj)) {
                match self {
                #( #trace_matches )*
                }
            }

            fn after_forwarding(&mut self) {
                match self {
                    #( #forwarding_matches )*
                }
            }
        }
    })
}

fn get_generic_arguments(generics: &syn::Generics) -> TokenStream2 {
    let generic_arguments = generics
        .params
        .iter()
        .map(|p| match p.clone() {
            syn::GenericParam::Type(t) => t.ident.into_token_stream(),
            syn::GenericParam::Lifetime(l) => l.lifetime.into_token_stream(),
            syn::GenericParam::Const(c) => c.ident.into_token_stream(),
        })
        .collect::<Vec<TokenStream2>>();
    if generic_arguments.is_empty() {
        TokenStream2::new()
    } else {
        quote! { <#( #generic_arguments ),*> }
    }
}
