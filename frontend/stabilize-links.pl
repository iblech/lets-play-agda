#!/usr/bin/env perl
# Rewrite Agda's unstable numeric link targets to stable name-based ones.
#
# Agda's HTML backend generates two anchors for each definition:
#   <a id="List"></a><a id="499" href="Foo.html#499" class="Datatype">List</a>
# The first is a stable name-based anchor, the second uses an unstable byte offset.
# All cross-references use the unstable numeric form.
#
# This script:
# 1. Scans all .html and .md files in the given directory for these pairs
# 2. Builds a mapping: "File.html#499" → "File.html#List"
# 3. Rewrites all href attributes to use stable anchors where possible
# 4. Strips links whose targets remain unstable (turns them into spans)
#
# Usage: ./stabilize-links.pl <directory> [--strip]
# With --strip, remaining links with unstable targets are turned into spans.

use strict;
use warnings;
use File::Find;
use File::Slurp;

my $dir   = shift @ARGV or die "Usage: $0 <directory> [--strip]\n";
my $strip = (shift @ARGV // '') eq '--strip';

# Step 1: Collect the mapping from unstable to stable anchors.
my %stable_for;  # "File.html#499" => "File.html#List"

my @files;
find(sub {
    push @files, $File::Find::name if /\.(html|md)$/;
}, $dir);

for my $file (@files) {
    my $content = read_file($file);

    # Match: <a id="STABLE"></a><a id="NUM" href="FILE#NUM"
    while ($content =~ m{<a\s+id="([^"]+)"></a><a\s+id="(\d+)"\s+href="([^"]*)\#(\d+)"}g) {
        my ($stable_id, $num_id, $href_file, $href_num) = ($1, $2, $3, $4);
        next if $stable_id =~ /^\d+$/;  # skip if "stable" id is also numeric
        $stable_for{"$href_file#$href_num"} = "$href_file#$stable_id";
    }
}

my $stabilized = 0;
my $stripped    = 0;

# Step 2: Rewrite all href attributes using the mapping.
#         Strip links whose targets remain unstable.
#         Remove numeric id attributes.
for my $file (@files) {
    my $content = read_file($file);
    my $changed = 0;

    # Stabilize hrefs where possible
    $content =~ s{href="([^"#]*#\d+)"}{
        my $old = $1;
        if (exists $stable_for{$old}) {
            $changed++;
            $stabilized++;
            qq{href="$stable_for{$old}"};
        } else {
            qq{href="$old"};
        }
    }ge;

    # Strip remaining links with unstable (numeric) fragment targets.
    # These links may have attributes in any order (id, href, class).
    if ($strip) {
        $content =~ s{<a\s(?=[^>]*href="[^"#]*#\d+")[^>]*class="([^"]*)">(.*?)</a>}{
            $changed++;
            $stripped++;
            qq{<span class="$1">$2</span>};
        }ge;
    }

    if ($changed) {
        write_file($file, $content);
    }
}

print "Stabilized $stabilized link(s), stripped $stripped link(s) across " . scalar(@files) . " file(s).\n";

# Step 3: Extract type signatures from definition sites and emit as JavaScript.
# A definition site has the pattern: <a...></a><a href="FILE#NAME" ...>TEXT</a>
# The type may span multiple lines (the colon and type on continuation lines).
my %type_of;  # "File.html#name" => "name : Type"

sub strip_html_line {
    my $line = shift;
    # Remove comments and 'where' keyword before stripping tags
    $line =~ s/<a[^>]*class="Comment"[^>]*>.*?<\/a>//g;
    $line =~ s/<a[^>]*class="Keyword"[^>]*>where<\/a>//g;
    # Strip all HTML tags
    $line =~ s/<[^>]*>//g;
    # Decode HTML entities
    $line =~ s/&#(\d+);/chr($1)/ge;
    $line =~ s/&#x([0-9a-fA-F]+);/chr(hex($1))/ge;
    $line =~ s/&lt;/</g;
    $line =~ s/&gt;/>/g;
    $line =~ s/&amp;/&/g;
    $line =~ s/&quot;/"/g;
    # Remove comments (-- ...) and any preceding whitespace
    $line =~ s/\s*--\s.*//;
    return $line;
}

for my $file (@files) {
    my $content = read_file($file);
    my @lines = split /\n/, $content;

    for my $i (0 .. $#lines) {
        my $line = $lines[$i];
        while ($line =~ m{<a[^>]*></a><a\s[^>]*href="([^"]+)"[^>]*>([^<]*)</a>}g) {
            my ($href, $name) = ($1, $2);

            # Decode HTML entities in href
            $href =~ s/&#(\d+);/chr($1)/ge;
            $href =~ s/&#x([0-9a-fA-F]+);/chr(hex($1))/ge;
            $href =~ s/&amp;/&/g;

            # Start with the definition line and collect continuation lines
            my $clean = strip_html_line($line);
            my $cont_start = $i + 1;

            # If no colon on this line, look ahead for it
            unless ($clean =~ /:/) {
                for my $j ($cont_start .. $#lines) {
                    my $next = strip_html_line($lines[$j]);
                    $clean .= ' ' . $next;
                    $cont_start = $j + 1;
                    last if $clean =~ /:/;
                }
            }

            # Collect the remaining type continuation lines
            # (indented lines, typically beginning with → or other symbols)
            if ($clean =~ /:/) {
                for my $j ($cont_start .. $#lines) {
                    my $next_raw = $lines[$j];
                    # Stop at non-indented lines (implementation or next definition)
                    last unless $next_raw =~ /^\s/;
                    # Stop at another definition site (e.g. constructors after 'where')
                    last if $next_raw =~ /<a[^>]*><\/a><a\s/;
                    # Stop at comment-only lines (e.g. -- Holify)
                    last if $next_raw =~ /^\s*<a class="Comment">/;
                    my $next = strip_html_line($next_raw);
                    # Stop if the continuation looks like an implementation
                    # (mentions the same name followed by arguments/=)
                    last if $next =~ /^\s*\Q$name\E\s/;
                    last if $next =~ /^\s*$/;
                    $clean .= ' ' . $next;
                }
            }

            # Detect data/record definitions before stripping the keyword
            my $keyword_prefix = '';
            if ($clean =~ /^\s*(?:data|record)\b/) {
                ($keyword_prefix) = $clean =~ /^\s*(data|record)/;
                $keyword_prefix .= ' ';
            }
            # Remove leading Agda keywords
            $clean =~ s/^\s*(?:data|record|postulate|field|constructor|instance|macro|abstract|private)\s+//;
            # Collapse and trim whitespace
            $clean =~ s/\s+/ /g;
            $clean =~ s/^\s+|\s+$//g;

            # Only keep entries that have a colon (i.e. a type signature)
            next unless $clean =~ /:/;
            # Skip pragma-only lines (BUILTIN etc.)
            next if $clean =~ /^\{-#/;

            $type_of{$href} = $keyword_prefix . $clean;
        }
    }
}

# Emit the type mapping as a JavaScript variable declaration.
{
    my $js_file = "$dir/type-signatures.js";
    open my $fh, '>', $js_file or die "Cannot write $js_file: $!\n";
    print $fh "const typeSignatures = {\n";
    for my $href (sort keys %type_of) {
        my $key = $href;
        my $val = $type_of{$href};
        # Escape for JS string literals
        $key =~ s/\\/\\\\/g; $key =~ s/"/\\"/g;
        $val =~ s/\\/\\\\/g; $val =~ s/"/\\"/g;
        print $fh "  \"$key\": \"$val\",\n";
    }
    print $fh "};\n";
    close $fh;
    print "Wrote " . scalar(keys %type_of) . " type signature(s) to $js_file.\n";
}
