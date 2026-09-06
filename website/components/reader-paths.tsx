'use client';
import {
  Children,
  isValidElement,
  useEffect,
  useRef,
  useState,
  type ReactNode,
} from 'react';
import { ArrowDown, ArrowRight, Plus, Minus } from 'lucide-react';
import { Button } from '@/components/ui/button';
import { ToggleGroup, ToggleGroupItem } from '@/components/ui/toggle-group';
import { useMotion } from '@/components/exhibit-motion';
import {
  chapterInfo,
  chapterForAnchor,
  decodeAnchor,
  omittedChapters,
  readerPaths,
  resolvePath,
  type ChapterId,
  type PathId,
} from '@/lib/reader-paths';

export function ReaderPaths({
  selected,
  depth,
  onChoose,
}: {
  selected: PathId;
  depth: string;
  onChoose: (id: PathId) => void;
}) {
  const path = resolvePath(selected);
  return (
    <section
      className="reader-paths"
      id="reader-paths"
      tabIndex={-1}
      aria-labelledby="reader-path-heading"
    >
      <div className="reader-path-intro">
        <div>
          <span className="eyebrow">FIND YOUR WAY IN</span>
          <h2 id="reader-path-heading">One argument. Your starting point.</h2>
        </div>
        <p>
          Choose what to open first. The page rearranges around the questions
          you bring.
        </p>
      </div>
      <ToggleGroup
        className="reader-path-choices"
        value={[selected]}
        onValueChange={(values) => {
          if (readerPaths.some((p) => p.id === values[0]))
            onChoose(values[0] as PathId);
        }}
        aria-label="Choose a reader path"
      >
        {readerPaths.map((p) => (
          <ToggleGroupItem value={p.id} key={p.id}>
            <strong>{p.label}</strong>
            <span>{p.description}</span>
          </ToggleGroupItem>
        ))}
      </ToggleGroup>
      <div className="path-opening" key={selected}>
        <span className="eyebrow">
          {path.chapters.length} CHAPTERS ·{' '}
          {depth === 'story'
            ? 'EQUATIONS FOLDED AWAY'
            : depth === 'math'
              ? 'MATHEMATICAL DETAILS OPEN'
              : 'INTERACTIVE EXPLANATIONS OPEN'}
        </span>
        <h3>{path.title}</h3>
        <p>{path.introduction}</p>
        <nav className="reader-path-stops" aria-label={path.label + ': route'}>
          {path.stops.map((s, i) => (
            <a key={s.id} href={'#' + s.id}>
              <span>0{i + 1}</span>
              {s.label}
              <ArrowRight size={14} />
            </a>
          ))}
          <a className="path-start" href={'#' + path.chapters[0]}>
            Start here <ArrowDown size={15} />
          </a>
        </nav>
      </div>
      <output className="sr-only">
        {path.label} selected. {path.chapters.length} chapters. The first
        chapter is {chapterInfo[path.chapters[0]].title}.
      </output>
    </section>
  );
}

export function PathChapter({
  children,
}: {
  chapter: ChapterId;
  children: ReactNode;
}) {
  return <>{children}</>;
}

export function PathFlow({
  selected,
  children,
}: {
  selected: PathId;
  children: ReactNode;
}) {
  const path = resolvePath(selected);
  const { enabled } = useMotion();
  const [expanded, setExpanded] = useState<ChapterId[]>([]);
  const [destination, setDestination] = useState('');
  const host = useRef<HTMLDivElement>(null);
  const chapters = new Map(
    Children.toArray(children)
      .filter(isValidElement)
      .map((child) => {
        const item = child as React.ReactElement<{ chapter: ChapterId }>;
        return [item.props.chapter, item];
      }),
  );
  const omitted = omittedChapters(selected);
  useEffect(() => {
    const follow = (id: string) => {
      const chapter = chapterForAnchor(id);
      if (!chapter) return false;
      if (!path.chapters.includes(chapter))
        setExpanded((old) => (old.includes(chapter) ? old : [...old, chapter]));
      setDestination(id);
      return true;
    };
    const click = (event: MouseEvent) => {
      if (
        event.defaultPrevented ||
        event.metaKey ||
        event.ctrlKey ||
        event.shiftKey ||
        event.altKey
      )
        return;
      const link =
        event.target instanceof Element
          ? event.target.closest('a[href^="#"]')
          : null;
      if (!link) return;
      const id = decodeAnchor(link.getAttribute('href')!);
      if (follow(id)) {
        event.preventDefault();
        history.pushState(history.state, '', '#' + encodeURIComponent(id));
      }
    };
    const hash = () => {
      if (location.hash) follow(decodeAnchor(location.hash));
    };
    document.addEventListener('click', click);
    window.addEventListener('hashchange', hash);
    hash();
    return () => {
      document.removeEventListener('click', click);
      window.removeEventListener('hashchange', hash);
    };
  }, [path]);
  useEffect(() => {
    if (!destination) return;
    const frame = requestAnimationFrame(() => {
      const element = document.getElementById(destination);
      if (!element) return;
      let parent: HTMLElement | null = element;
      while (parent) {
        if (parent instanceof HTMLDetailsElement) parent.open = true;
        parent = parent.parentElement;
      }
      element.tabIndex = -1;
      element.focus({ preventScroll: true });
      element.scrollIntoView({
        behavior: enabled ? 'smooth' : 'instant',
        block: 'start',
      });
      setDestination('');
    });
    return () => cancelAnimationFrame(frame);
  }, [destination, expanded, enabled]);
  return (
    <div className="path-flow" data-reader-path={selected} ref={host}>
      {path.chapters.map((chapter, index) => (
        <div className="path-chapter" data-chapter={chapter} key={chapter}>
          {path.bridges[chapter] && (
            <div className="path-bridge">
              <span>
                {String(index + 1).padStart(2, '0')} / {path.chapters.length}
              </span>
              <p>{path.bridges[chapter]}</p>
            </div>
          )}
          {chapters.get(chapter)}
          <div className="path-next">
            {index + 1 < path.chapters.length ? (
              <a href={'#' + path.chapters[index + 1]}>
                <span>NEXT</span>
                {chapterInfo[path.chapters[index + 1]].title}
                <ArrowDown size={16} />
              </a>
            ) : (
              <a href="#reader-paths">
                <span>GO FURTHER</span>Choose another route through the argument{' '}
                <ArrowRight size={16} />
              </a>
            )}
          </div>
        </div>
      ))}
      {omitted.length > 0 && (
        <section className="path-further" aria-labelledby="further-heading">
          <span className="eyebrow">OPEN ANOTHER PART OF THE STORY</span>
          <h2 id="further-heading">The background is still here.</h2>
          <p>
            These chapters sit outside your chosen route. Open any of them
            without changing paths.
          </p>
          {omitted.map((chapter) => (
            <div className="optional-chapter" key={chapter}>
              <Button
                variant="ghost"
                className="optional-heading"
                aria-expanded={expanded.includes(chapter)}
                aria-controls={'optional-' + chapter}
                onClick={() =>
                  setExpanded((old) =>
                    old.includes(chapter)
                      ? old.filter((c) => c !== chapter)
                      : [...old, chapter],
                  )
                }
              >
                <span>
                  <strong>{chapterInfo[chapter].title}</strong>
                  <small>{chapterInfo[chapter].summary}</small>
                </span>
                {expanded.includes(chapter) ? (
                  <Minus size={20} />
                ) : (
                  <Plus size={20} />
                )}
              </Button>
              <div id={'optional-' + chapter}>
                {expanded.includes(chapter) ? chapters.get(chapter) : null}
              </div>
            </div>
          ))}
        </section>
      )}
    </div>
  );
}
