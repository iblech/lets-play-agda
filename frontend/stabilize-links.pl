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
# Usage: ./stabilize-links.pl <directory>

use strict;
use warnings;
use File::Find;
use File::Slurp;

my $dir = shift @ARGV or die "Usage: $0 <directory>\n";

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
    $content =~ s{<a\s(?=[^>]*href="[^"#]*#\d+")[^>]*class="([^"]*)">(.*?)</a>}{
        $changed++;
        $stripped++;
        qq{<span class="$1">$2</span>};
    }ge;

    if ($changed) {
        write_file($file, $content);
    }
}

print "Stabilized $stabilized link(s), stripped $stripped link(s) across " . scalar(@files) . " file(s).\n";
